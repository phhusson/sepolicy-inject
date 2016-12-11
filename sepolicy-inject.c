/*
 * This was derived from public domain works with updates to
 * work with more modern SELinux libraries.
 *
 * It is released into the public domain.
 *
 */

#include <getopt.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdint.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>
#include <sepol/debug.h>
#include <sepol/policydb/policydb.h>
#include <sepol/policydb/expand.h>
#include <sepol/policydb/link.h>
#include <sepol/policydb/services.h>
#include <sepol/policydb/avrule_block.h>
#include <sepol/policydb/conditional.h>
#include <sepol/policydb/constraint.h>

extern int policydb_index_decls(policydb_t *p);

void usage(const char *arg0)
{
	fprintf(stderr, "%s -s <source type> -t <target type> -c <class> -p <perm_list> -P <policy file>\n", arg0);
	fprintf(stderr, "\tInject a rule\n\n");
	fprintf(stderr, "%s -s <source type> -a <type_attribute> -P <policy file>\n", arg0);
	fprintf(stderr, "\tAdd a type_attribute to a domain\n\n");
	fprintf(stderr, "%s -Z <source type> -P <policy file>\n", arg0);
	fprintf(stderr, "\tInject a permissive domain\n\n");
	fprintf(stderr, "%s -z <source type> -P <policy file>\n", arg0);
	fprintf(stderr, "\tInject a non-permissive domain\n\n");
	fprintf(stderr, "%s -e -s <source type> -P <policy file>\n", arg0);
	fprintf(stderr, "\tCheck if a SELinux type exists\n\n");
	fprintf(stderr, "%s -e -c <class> -P <policy file>\n", arg0);
	fprintf(stderr, "\tCheck if a SELinux class exists\n\n");
	fprintf(stderr, "All options can add -o <output file> to output to another file\n");
	exit(1);
}

void *cmalloc(const size_t s)
{
	void *t = malloc(s);
	if (!t) {
		fprintf(stderr, "Out of memory\n");
		exit(1);
	}
	return t;
}

type_datum_t *get_attr(char *type, policydb_t *policy)
{
	type_datum_t *attr;

	if (!(attr = hashtab_search(policy->p_types.table, type)))
		return NULL;

	if (attr->flavor != TYPE_ATTRIB)
		return NULL;

	return attr;
}

int get_attr_id(char *type, policydb_t *policy)
{
	type_datum_t *attr = get_attr(type, policy);

	return attr ? (int)attr->s.value : -1;
}

int set_attr(char *type, const int value, policydb_t *policy)
{
	type_datum_t *attr = get_attr(type, policy);

	if (!attr)
		return 1;

	if (ebitmap_set_bit(&policy->type_attr_map[value-1], attr->s.value - 1, 1))
		return 1;
	if (ebitmap_set_bit(&policy->attr_type_map[attr->s.value-1], value - 1, 1))
		return 1;

	return 0;
}

type_datum_t *create_domain(char *d, policydb_t *policy)
{
	uint32_t value = 0;
	unsigned i;
	int r;
	type_datum_t *src;

	if ((src = hashtab_search(policy->p_types.table, d))) {
		printf("Domain '%s' already exists\n", d);
		return src;
	}

	src = cmalloc(sizeof(type_datum_t));
	type_datum_init(src);
	src->primary = 1;
	src->flavor = TYPE_TYPE;

	r = symtab_insert(policy, SYM_TYPES, strdup(d), src,
			  SCOPE_DECL, 1, &value);
	src->s.value = value;

	if (ebitmap_set_bit(&policy->global->branch_list->declared.scope[SYM_TYPES], value - 1, 1))
		goto fail;

	policy->type_attr_map = realloc(policy->type_attr_map, sizeof(ebitmap_t)*policy->p_types.nprim);
	policy->attr_type_map = realloc(policy->attr_type_map, sizeof(ebitmap_t)*policy->p_types.nprim);
	ebitmap_init(&policy->type_attr_map[value - 1]);
	ebitmap_init(&policy->attr_type_map[value - 1]);
	ebitmap_set_bit(&policy->type_attr_map[value - 1], value - 1, 1);

	//Add the domain to all roles
	for (i = 0; i < policy->p_roles.nprim; i++) {
		//Not sure all those three calls are needed
		ebitmap_set_bit(&policy->role_val_to_struct[i]->types.negset, value - 1, 0);
		ebitmap_set_bit(&policy->role_val_to_struct[i]->types.types, value - 1, 1);
		type_set_expand(&policy->role_val_to_struct[i]->types, &policy->role_val_to_struct[i]->cache, policy, 0);
	}

	if (!(src = hashtab_search(policy->p_types.table, d)))
		goto fail;

	if (policydb_index_decls(policy))
		goto fail;

	if (policydb_index_classes(policy))
		goto fail;

	if (policydb_index_others(NULL, policy, 0))
		goto fail;

	if (set_attr("domain", value, policy))
		goto fail;

	printf("Created domain '%s'\n", d);

	return src;
fail:
	fprintf(stderr, "Failed to create domain '%s'\n", d);
	if (src)
		free(src);
	return NULL;
}

int add_irule(const int s, const int t, const int c, const int p,
	      const int effect, const int not, policydb_t* policy)
{
	int ret = 0;
	unsigned avd = 1U << (p - 1);
	avtab_datum_t *av;
	avtab_key_t key;

	key.source_type = s;
	key.target_type = t;
	key.target_class = c;
	key.specified = effect;

	if (!(av = avtab_search(&policy->te_avtab, &key))) {
		av = cmalloc(sizeof(*av));
		av->data |= avd;
		if ((ret = avtab_insert(&policy->te_avtab, &key, av))) {
			fprintf(stderr, "Error inserting into avtab\n");
			return 1;
		}
	}

	if (not)
		av->data &= ~avd;
	else
		av->data |= avd;

	return 0;
}

int add_rule_auto(type_datum_t *src, type_datum_t *tgt, class_datum_t *cls,
		  perm_datum_t *perm, const int effect, const int not,
		  policydb_t *policy)
{
	unsigned i;
	hashtab_t table;
	hashtab_ptr_t cur;

	if (!src) {
		table = policy->p_types.table;
		for (i = 0; i < table->size; i++) {
			cur = table->htable[i];
			while (cur) {
				src = cur->datum;
				if (add_rule_auto(src, tgt, cls, perm,
						  effect, not, policy))
					return 1;
				cur = cur->next;
			}
		}
	} else if (!tgt) {
		table = policy->p_types.table;
		for (i = 0; i < table->size; i++) {
			cur = table->htable[i];
			while (cur) {
				tgt = cur->datum;
				if (add_rule_auto(src, tgt, cls, perm,
						  effect, not, policy))
					return 1;
				cur = cur->next;
			}
		}
	} else if (!cls) {
		table = policy->p_classes.table;
		for (i = 0; i < table->size; i++) {
			cur = table->htable[i];
			while (cur) {
				cls = cur->datum;
				if (add_rule_auto(src, tgt, cls, perm,
						  effect, not, policy))
					return 1;
				cur = cur->next;
			}
		}
	} else if (!perm) {
		table = cls->permissions.table;
		for (i = 0; i < table->size; i++) {
			cur = table->htable[i];
			while (cur) {
				perm = cur->datum;
				if (add_irule(src->s.value, tgt->s.value,
					      cls->s.value, perm->s.value,
					      effect, not, policy))
					return 1;
				cur = cur->next;
			}
		}

		if (!cls->comdatum)
			return 0;

		table = cls->comdatum->permissions.table;
		for (i = 0; i < table->size; i++) {
			cur = table->htable[i];
			while (cur) {
				perm = cur->datum;
				if (add_irule(src->s.value, tgt->s.value,
					      cls->s.value, perm->s.value,
					      effect, not, policy))
					return 1;
				cur = cur->next;
			}
		}
	} else {
		return add_irule(src->s.value, tgt->s.value, cls->s.value,
				 perm->s.value, effect, not, policy);
	}

	return 0;
}

int add_rule(char *s, char *t, char *c, char *p,
	     const int effect, const int not, policydb_t *policy)
{
	int ret = 0;
	type_datum_t *src = NULL, *tgt = NULL;
	class_datum_t *cls = NULL;
	perm_datum_t *perm = NULL;

	if (s && !(src = hashtab_search(policy->p_types.table, s))) {
		fprintf(stderr, "Source type '%s' does not exist\n", s);
		ret = 1;
	}
	if (t && !(tgt = hashtab_search(policy->p_types.table, t))) {
		fprintf(stderr, "Target type '%s' does not exist\n", t);
		ret = 1;
	}
	if (c && !(cls = hashtab_search(policy->p_classes.table, c))) {
		fprintf(stderr, "Class '%s' does not exist\n", c);
		ret = 1;
	}
	if (p && !c) {
		fprintf(stderr, "No class is specified, cannot add perm '%s'\n", p);
		ret = 1;
	}
	if (ret)
		return ret;

	if (p) {
		perm = hashtab_search(cls->permissions.table, p);
		if (!perm && cls->comdatum)
			perm = hashtab_search(cls->comdatum->permissions.table, p);

		if (!perm) {
			fprintf(stderr,
				"Perm '%s' does not exist in class '%s'\n",
				p, c);
			return 1;
		}
	}

	return add_rule_auto(src, tgt, cls, perm, effect, not, policy);
}

int add_typerule(char *s, char *a, char **minusses, char *c,
		 char *p, const int effect, const int not, policydb_t *policy)
{
	int ret = 0;
	unsigned i;
	type_datum_t *src, *tgt, *obj;
	class_datum_t *cls;
	perm_datum_t *perm;
	ebitmap_node_t *node;

	//64(0kB) should be enough for everyone, right?
	int m[64] = { -1 };

	if (!(src = hashtab_search(policy->p_types.table, s))) {
		fprintf(stderr, "source type '%s' does not exist\n", s);
		ret = 1;
	}
	if (!(tgt = hashtab_search(policy->p_types.table, a))) {
		fprintf(stderr, "target type '%s' does not exist\n", a);
		ret = 1;
	}
	if (!(cls = hashtab_search(policy->p_classes.table, c))) {
		fprintf(stderr, "class '%s' does not exist\n", c);
		ret = 1;
	}
	if (ret)
		return ret;

	if (tgt->flavor != TYPE_ATTRIB)
		exit(1);

	for (i = 0; minusses && minusses[i]; ++i) {
		if (!(obj = hashtab_search(policy->p_types.table,
					   minusses[i]))) {
			fprintf(stderr, "minus type '%s' does not exist\n",
				minusses[i]);
			return 1;
		}
		m[i] = obj->s.value-1;
		m[i+1] = -1;
	}

	if (!cls->comdatum) {
		fprintf(stderr, "class '%s' is empty\n", c);
		return 1;
	}
	if (!(perm = hashtab_search(cls->permissions.table, p))) {
		if (!(perm = hashtab_search(
				cls->comdatum->permissions.table, p))) {
			fprintf(stderr,
				"perm '%s' does not exist in class '%s'\n",
				p, c);
			return 1;
		}
	}

	ebitmap_for_each_bit(&policy->attr_type_map[tgt->s.value-1], node, i) {
		if (ebitmap_node_get_bit(node, i)) {
			int found = 0;
			for (unsigned j = 0; m[j] != -1; j++) {
				if (i == (unsigned)m[j]) {
					found = 1;
					break;
				}
			}
			if (found)
				continue;

			ret |= add_irule(src->s.value, i + 1, cls->s.value,
					 perm->s.value, effect, not, policy);
		}
	}

	return ret;
}

int add_transition(char *srcS, char *origS, char *tgtS,
		   char *c, policydb_t *policy)
{
	int ret = 0;
	type_datum_t *src, *tgt, *orig;
	class_datum_t *cls;
	avtab_datum_t *av;
	avtab_key_t key;

	if (!(src = hashtab_search(policy->p_types.table, srcS))) {
		fprintf(stderr, "Source type '%s' does not exist\n", srcS);
		ret = 1;
	}
	if (!(orig = hashtab_search(policy->p_types.table, origS))) {
		fprintf(stderr, "Origin type '%s' does not exist\n", origS);
		ret = 1;
	}
	if (!(tgt = hashtab_search(policy->p_types.table, tgtS))) {
		fprintf(stderr, "Target type '%s' does not exist\n", tgtS);
		ret = 1;
	}
	if (!(cls = hashtab_search(policy->p_classes.table, c))) {
		fprintf(stderr, "Class '%s' does not exist\n", c);
		ret = 1;
	}
	if (ret)
		return ret;

	key.source_type  = src->s.value;
	key.target_type  = orig->s.value;
	key.target_class = cls->s.value;
	key.specified    = AVTAB_TRANSITION;

	if (!(av = avtab_search(&policy->te_avtab, &key))) {
		av = cmalloc(sizeof(*av));
		av->data = tgt->s.value;

		if ((ret = avtab_insert(&policy->te_avtab, &key, av))) {
			fprintf(stderr, "Error inserting into avtab\n");
			return ret;
		}
	} else {
		fprintf(stderr, "Warning, rule already defined! Won't override.\n");
		fprintf(stderr, "Previous value = %d, wanted value = %d\n",
			av->data, tgt->s.value);
	}

	return ret;
}

int add_file_transition(char *srcS, char *origS, char *tgtS,
			char *c, char* filename, policydb_t *policy)
{
	int ret = 0;
	type_datum_t *src, *tgt, *orig;
	class_datum_t *cls;
	filename_trans_t *new_transition;

	if (!(src = hashtab_search(policy->p_types.table, srcS))) {
		fprintf(stderr, "Source type '%s' does not exist\n", srcS);
		ret = 1;
	}
	if (!(orig = hashtab_search(policy->p_types.table, origS))) {
		fprintf(stderr, "Origin type '%s' does not exist\n", origS);
		ret = 1;
	}
	if (!(tgt = hashtab_search(policy->p_types.table, tgtS))) {
		fprintf(stderr, "Target type '%s' does not exist\n", tgtS);
		ret = 1;
	}
	if (!(cls = hashtab_search(policy->p_classes.table, c))) {
		fprintf(stderr, "Class '%s' does not exist\n", c);
		ret = 1;
	}
	if (ret)
		return ret;

	new_transition = cmalloc(sizeof(*new_transition));
	new_transition->stype  = src->s.value;
	new_transition->ttype  = orig->s.value;
	new_transition->otype  = tgt->s.value;
	new_transition->tclass = cls->s.value;
	new_transition->name   = strdup(filename);
	new_transition->next   = policy->filename_trans;

	policy->filename_trans = new_transition;

	return ret;
}

int add_type(char *domainS, char *typeS, policydb_t *policy)
{
	int typeId;
	uint32_t i;
	type_datum_t *domain;
	class_datum_t *cl;
	constraint_node_t *n;
	constraint_expr_t *e;

	if (!(domain = hashtab_search(policy->p_types.table, domainS))) {
		fprintf(stderr, "Domain '%s' does not exist\n", domainS);
		return 1;
	}

	set_attr(typeS, domain->s.value, policy);

	typeId = get_attr_id(typeS, policy);
	if (typeId == -1)
		return 1;

	//Now let's update all constraints!
	//(kernel doesn't support (yet?) type_names rules)
	for (i = 0; i < policy->p_classes.nprim; i++) {
		cl = policy->class_val_to_struct[i];
		for (n = cl->constraints; n; n = n->next) {
			for (e = n->expr; e; e = e->next) {
				if (e->expr_type != CEXPR_NAMES)
					continue;
				if (ebitmap_get_bit(&e->type_names->types, typeId - 1))
					ebitmap_set_bit(&e->names, domain->s.value - 1, 1);
			}
		}
	}

	return 0;
}

void print_policy_info(policydb_t *p, FILE *fp)
{
	if (!p) {
		fprintf(fp, "Could not read policydb!\n");
		return;
	}

	fprintf(fp, "%d users, %d roles, %d types, %d bools",
		p->p_users.nprim, p->p_roles.nprim, p->p_types.nprim,
		p->p_bools.nprim);

	if (p->mls)
		fprintf(fp, ", %d sens, %d cats",
			p->p_levels.nprim, p->p_cats.nprim);

	fprintf(fp, ", %d classes, %d rules, %d cond rules",
		p->p_classes.nprim, p->te_avtab.nel, p->te_cond_avtab.nel);

	fprintf(fp, "\n");
}

int load_policy(const char *filename,
		policydb_t *policydb, struct policy_file *pf)
{
	int ret = 0;
	struct stat sb;
	void *map;

	int fd = open(filename, O_RDONLY);
	if (fd < 0) {
		fprintf(stderr, "Can't open '%s':  %s\n",
			filename, strerror(errno));
		return 1;
	}
	if (fstat(fd, &sb) < 0) {
		fprintf(stderr, "Can't stat '%s':  %s\n",
			filename, strerror(errno));
		return 1;
	}
	map = mmap(NULL, sb.st_size, PROT_READ|PROT_WRITE, MAP_PRIVATE, fd, 0);
	if (map == MAP_FAILED) {
		fprintf(stderr, "Can't mmap '%s':  %s\n",
			filename, strerror(errno));
		return 1;
	}

	policy_file_init(pf);
	pf->type = PF_USE_MEMORY;
	pf->data = map;
	pf->len = sb.st_size;

	if (policydb_init(policydb)) {
		fprintf(stderr, "policydb_init: Out of memory!\n");
		return 1;
	}

	if ((ret = policydb_read(policydb, pf, 0)))
		fprintf(stderr,
			"error(s) encountered while parsing configuration\n");

	return ret;
}

int main(int argc, char **argv)
{
	char *policy = NULL, *source = NULL, *target = NULL,
		*class = NULL, *perm = NULL, *fcon = NULL,
		*outfile = NULL, *permissive = NULL,
		*attr = NULL, *filetrans = NULL;
	int ch, exists = 0, not = 0, permissive_value = 0, noaudit = 0, ret = 0;
	sidtab_t sidtab;
	policydb_t policydb;
	struct policy_file pf, outpf;
	FILE *fp;

	struct option long_options[] = {
		{"attr", required_argument, NULL, 'a'},
		{"exists", no_argument, NULL, 'e'},
		{"source", required_argument, NULL, 's'},
		{"target", required_argument, NULL, 't'},
		{"class", required_argument, NULL, 'c'},
		{"perm", required_argument, NULL, 'p'},
		{"fcon", required_argument, NULL, 'f'},
		{"filetransition", required_argument, NULL, 'g'},
		{"noaudit", no_argument, NULL, 'n'},
		{"policy", required_argument, NULL, 'P'},
		{"output", required_argument, NULL, 'o'},
		{"permissive", required_argument, NULL, 'Z'},
		{"not-permissive", required_argument, NULL, 'z'},
		{"not", no_argument, NULL, 0},
		{NULL, 0, NULL, 0}
	};

	int option_index = -1;
	while ((ch = getopt_long(argc, argv, "a:c:ef:g:s:t:p:P:o:Z:z:n",
				 long_options, &option_index)) != -1) {
		switch (ch) {
		case 0:
			if (!strcmp(long_options[option_index].name, "not"))
				not = 1;
			else
				usage(argv[0]);
			break;
		case 'a':
			attr = optarg;
			break;
		case 'e':
			exists = 1;
			break;
		case 'f':
			fcon = optarg;
			break;
		case 'g':
			filetrans = optarg;
			break;
		case 's':
			source = optarg;
			break;
		case 't':
			target = optarg;
			break;
		case 'c':
			class = optarg;
			break;
		case 'p':
			perm = optarg;
			break;
		case 'P':
			policy = optarg;
			break;
		case 'o':
			outfile = optarg;
			break;
		case 'Z':
			permissive = optarg;
			permissive_value = 1;
			break;
		case 'z':
			permissive = optarg;
			permissive_value = 0;
			break;
		case 'n':
			noaudit = 1;
			break;
		default:
			usage(argv[0]);
		}
	}

	if (!policy || ((!source || !target || !class || !perm)
			&& !permissive && !fcon && !attr
			&& !filetrans && !exists))
		usage(argv[0]);

	if (!outfile)
		outfile = policy;

	sepol_set_policydb(&policydb);
	sepol_set_sidtab(&sidtab);

	if (load_policy(policy, &policydb, &pf) ||
	    policydb_load_isids(&policydb, &sidtab)) {
		print_policy_info(&policydb, stderr);
		fprintf(stderr, "Could not load policy\n");
		return 1;
	}

	printf("Loaded policy: ");
	print_policy_info(&policydb, stdout);

	if (permissive) {
		type_datum_t *type;

		if (!(type = create_domain(permissive, &policydb))) {
			fprintf(stderr, "Could not create domain '%s'\n",
				permissive);
			return 1;
		}
		if (ebitmap_set_bit(&policydb.permissive_map,
				    type->s.value, permissive_value)) {
			fprintf(stderr, "Could not set bit in permissive map\n");
			return 1;
		}
		printf("Set permissive value of domain '%s' to %d\n",
			permissive, permissive_value);
	} else if (exists) {
		if (source) {
			type_datum_t *tmp = hashtab_search(policydb.p_types.table, source);
			printf("Source type '%s' %s in the policy\n", source,
				tmp ? "exists" : "does not exist");
			return !!tmp;
		}
		if (class) {
			class_datum_t *tmp = hashtab_search(policydb.p_classes.table, class);
			printf("Class '%s' %s in the policy\n", class,
				tmp ? "exists" : "does not exist");
			return !!tmp;
		}
		usage(argv[0]);
	} else if (filetrans) {
		if (add_file_transition(source, fcon, target,
					class, filetrans, &policydb))
			return 1;
		printf("Added file transition ("
			"file name '%s', source type '%s', "
			"file context '%s', target type '%s', "
			"class '%s')\n",
			filetrans, source, fcon, target, class);
	} else if (fcon) {
		if (add_transition(source, fcon, target, class, &policydb))
			return 1;
		printf("Added transition ("
			"source type '%s', file context '%s', "
			"target type '%s', class '%s')\n",
			source, fcon, target, class);
	} else if (attr) {
		if (add_type(source, attr, &policydb))
			return 1;
		printf("Added attr '%s' to source type '%s'\n", attr, source);
	} else if (noaudit) {
		if (add_rule(source, target, class, perm,
			     AVTAB_AUDITDENY, not, &policydb))
			return 1;
		printf("Added %s rule ("
			"source type '%s', target type '%s', "
			"class '%s', perm '%s')\n",
			not ? "audit" : "noaudit",
			source, target, class, perm);
	} else {
		//Add a rule to a whole set of typeattribute, not just a type
		if (target && *target == '=') {
			char *saveptr = NULL, *m = NULL;
			char *vals[64];
			char *a = strtok_r(target, "-", &saveptr);
			int i = 0;

			while ((m = strtok_r(NULL, "-", &saveptr)))
				vals[i++] = m;
			vals[i] = NULL;

			if (add_typerule(source, a + 1,
					 vals, class, perm, AVTAB_ALLOWED,
					 not, &policydb))
				return 1;
			printf("Added %s type rule ("
				"source type '%s', target type '%s', "
				"class '%s', perm '%s')\n",
				not ? "deny" : "allow",
				source, a + 1, class, perm);
		}
		if (perm) {
			char *saveptr = NULL;
			char *p = strtok_r(perm, ",", &saveptr);

			do {
				if (add_rule(source, target, class, p,
					     AVTAB_ALLOWED, not, &policydb)) {
					fprintf(stderr, "Could not add rule\n");
					return 1;
				}
				printf("Added %s rule ("
					"source type '%s', target type '%s', "
					"class '%s', perm '%s')\n",
					not ? "deny" : "allow",
					source, target, class, p);
			} while ((p = strtok_r(NULL, ",", &saveptr)));
		} else {
			if (add_rule(source, target, class, NULL,
				     AVTAB_ALLOWED, not, &policydb)) {
				fprintf(stderr, "Could not add rule\n");
				return 1;
			}
			printf("Added %s rule ("
				"source type '%s', target type '%s', "
				"class '%s')\n",
				not ? "deny" : "allow",
				source, target, class);
		}
	}

	if (!(fp = fopen(outfile, "w"))) {
		fprintf(stderr, "Could not open outfile\n");
		return 1;
	}

	policy_file_init(&outpf);
	outpf.type = PF_USE_STDIO;
	outpf.fp = fp;

	printf("New policy: ");
	print_policy_info(&policydb, stdout);

	if ((ret = policydb_write(&policydb, &outpf)))
		fprintf(stderr, "Could not write policy\n");

	policydb_destroy(&policydb);
	fclose(fp);

	return ret;
}
