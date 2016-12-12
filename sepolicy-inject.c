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
#include <fcntl.h>
#include <stdio.h>
#include <errno.h>
#include <sepol/debug.h>
#include <sepol/policydb/policydb.h>
#include <sepol/policydb/expand.h>
#include <sepol/policydb/link.h>
#include <sepol/policydb/services.h>
#include <sepol/policydb/avrule_block.h>
#include <sepol/policydb/conditional.h>
#include <sepol/policydb/constraint.h>

#define pr_info(fmt, ...) fprintf(stdout, fmt "\n", ##__VA_ARGS__)
#define pr_err(fmt, ...)  fprintf(stderr, fmt "\n", ##__VA_ARGS__)

static const char policy_load[] = "/sys/fs/selinux/load";
static const char policy_live[] = "/sys/fs/selinux/policy";

extern int policydb_index_decls(policydb_t *p);

static void usage(const char *arg0)
{
	pr_err("%s -s <source type> -t <target type> -c <class> -p <perm_list> -P <policy file>", arg0);
	pr_err("\tInject a rule\n");
	pr_err("%s -s <source type> -t <target type> -c <class> -p <perm_list> --live", arg0);
	pr_err("\tInject a rule into the running policy\n");
	pr_err("%s -s <source type> -a <type_attribute> -P <policy file>", arg0);
	pr_err("\tAdd a type_attribute to a domain\n");
	pr_err("%s -Z <source type> -P <policy file>", arg0);
	pr_err("\tInject a permissive domain\n");
	pr_err("%s -z <source type> -P <policy file>", arg0);
	pr_err("\tInject a non-permissive domain\n");
	pr_err("%s -e -s <source type> -P <policy file>", arg0);
	pr_err("\tCheck if a SELinux type exists\n");
	pr_err("%s -e -c <class> -P <policy file>", arg0);
	pr_err("\tCheck if a SELinux class exists\n");
	pr_err("All options can add -o <output file> to output to another file\n");
	exit(1);
}

static void *cmalloc(const size_t s)
{
	void *t = malloc(s);
	if (!t) {
		pr_err("Out of memory");
		exit(ENOMEM);
	}
	return t;
}

static type_datum_t *get_attr(char *type, policydb_t *policy)
{
	type_datum_t *attr;

	if (!(attr = hashtab_search(policy->p_types.table, type)))
		return NULL;

	if (attr->flavor != TYPE_ATTRIB)
		return NULL;

	return attr;
}

static unsigned get_attr_id(char *type, policydb_t *policy)
{
	type_datum_t *attr = get_attr(type, policy);

	return attr ? attr->s.value : 0;
}

static int set_attr(char *type, const int value, policydb_t *policy)
{
	type_datum_t *attr = get_attr(type, policy);

	if (!attr)
		return EINVAL;

	if (ebitmap_set_bit(&policy->type_attr_map[value-1], attr->s.value - 1, 1))
		return EINVAL;
	if (ebitmap_set_bit(&policy->attr_type_map[attr->s.value-1], value - 1, 1))
		return EINVAL;

	return 0;
}

static type_datum_t *create_domain(char *d, policydb_t *policy)
{
	uint32_t value = 0;
	unsigned i;
	int r;
	type_datum_t *src;

	if ((src = hashtab_search(policy->p_types.table, d))) {
		pr_info("Domain '%s' already exists", d);
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

	/* add the domain to all roles */
	for (i = 0; i < policy->p_roles.nprim; i++) {
		/* not sure all those three calls are needed */
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

	pr_info("Created domain '%s'", d);

	return src;
fail:
	pr_err("Failed to create domain '%s'", d);
	if (src)
		free(src);
	return NULL;
}

static int add_irule(const int s, const int t, const int c, const int p,
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
			pr_err("Error inserting into avtab");
			return ret;
		}
	}

	if (not)
		av->data &= ~avd;
	else
		av->data |= avd;

	return ret;
}

static int add_rule_auto(type_datum_t *src, type_datum_t *tgt,
			 class_datum_t *cls, perm_datum_t *perm,
			 const int effect, const int not, policydb_t *policy)
{
	int ret = 0;
	unsigned i;
	hashtab_t table;
	hashtab_ptr_t cur;

	if (!src) {
		table = policy->p_types.table;
		for (i = 0; i < table->size; i++) {
			cur = table->htable[i];
			while (cur) {
				src = cur->datum;
				if ((ret = add_rule_auto(src, tgt, cls, perm,
							 effect, not, policy)))
					return ret;
				cur = cur->next;
			}
		}
	} else if (!tgt) {
		table = policy->p_types.table;
		for (i = 0; i < table->size; i++) {
			cur = table->htable[i];
			while (cur) {
				tgt = cur->datum;
				if ((ret = add_rule_auto(src, tgt, cls, perm,
							 effect, not, policy)))
					return ret;
				cur = cur->next;
			}
		}
	} else if (!cls) {
		table = policy->p_classes.table;
		for (i = 0; i < table->size; i++) {
			cur = table->htable[i];
			while (cur) {
				cls = cur->datum;
				if ((ret = add_rule_auto(src, tgt, cls, perm,
							 effect, not, policy)))
					return ret;
				cur = cur->next;
			}
		}
	} else if (!perm) {
		table = cls->permissions.table;
		for (i = 0; i < table->size; i++) {
			cur = table->htable[i];
			while (cur) {
				perm = cur->datum;
				if ((ret = add_irule(src->s.value, tgt->s.value,
						     cls->s.value, perm->s.value,
						     effect, not, policy)))
					return ret;
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
				if ((ret = add_irule(src->s.value, tgt->s.value,
						     cls->s.value, perm->s.value,
						     effect, not, policy)))
					return ret;
				cur = cur->next;
			}
		}
	} else {
		return add_irule(src->s.value, tgt->s.value, cls->s.value,
				 perm->s.value, effect, not, policy);
	}

	return ret;
}

static int add_rule(char *s, char *t, char *c, char *p,
		    const int effect, const int not, policydb_t *policy)
{
	int ret = 0;
	type_datum_t *src = NULL, *tgt = NULL;
	class_datum_t *cls = NULL;
	perm_datum_t *perm = NULL;

	if (s && !(src = hashtab_search(policy->p_types.table, s))) {
		pr_err("Source type '%s' does not exist", s);
		ret = EINVAL;
	}
	if (t && !(tgt = hashtab_search(policy->p_types.table, t))) {
		pr_err("Target type '%s' does not exist", t);
		ret = EINVAL;
	}
	if (c && !(cls = hashtab_search(policy->p_classes.table, c))) {
		pr_err("Class '%s' does not exist", c);
		ret = EINVAL;
	}
	if (p && !c) {
		pr_err("No class is specified, cannot add perm '%s'", p);
		ret = EINVAL;
	}
	if (ret)
		return ret;

	if (p) {
		perm = hashtab_search(cls->permissions.table, p);
		if (!perm && cls->comdatum)
			perm = hashtab_search(cls->comdatum->permissions.table, p);

		if (!perm) {
			pr_err("Perm '%s' does not exist in class '%s'", p, c);
			return EINVAL;
		}
	}

	return add_rule_auto(src, tgt, cls, perm, effect, not, policy);
}

static int add_typerule(char *s, char *a, char **minusses, char *c,
			char *p, const int effect, const int not, policydb_t *policy)
{
	int ret = 0;
	unsigned i;
	type_datum_t *src, *tgt, *obj;
	class_datum_t *cls;
	perm_datum_t *perm;
	ebitmap_node_t *node;

	/* 64(0kB) should be enough for everyone, right? */
	int m[64] = { -1 };

	if (!(src = hashtab_search(policy->p_types.table, s))) {
		pr_err("Source type '%s' does not exist", s);
		ret = EINVAL;
	}
	if (!(tgt = hashtab_search(policy->p_types.table, a))) {
		pr_err("Target type '%s' does not exist", a);
		ret = EINVAL;
	}
	if (!(cls = hashtab_search(policy->p_classes.table, c))) {
		pr_err("Class '%s' does not exist", c);
		ret = EINVAL;
	}
	if (ret)
		return ret;

	if (tgt->flavor != TYPE_ATTRIB)
		return EINVAL;

	for (i = 0; minusses && minusses[i]; ++i) {
		if (!(obj = hashtab_search(policy->p_types.table,
					   minusses[i]))) {
			pr_err("Minus type '%s' does not exist", minusses[i]);
			return EINVAL;
		}
		m[i] = obj->s.value-1;
		m[i+1] = -1;
	}

	if (!cls->comdatum) {
		pr_err("Class '%s' has no permissions table", c);
		return EINVAL;
	}

	if (!(perm = hashtab_search(cls->permissions.table, p))) {
		if (!(perm = hashtab_search(
				cls->comdatum->permissions.table, p))) {
			pr_err("Perm '%s' does not exist in class '%s'", p, c);
			return EINVAL;
		}
	}

	ebitmap_for_each_bit(&policy->attr_type_map[tgt->s.value-1], node, i) {
		if (ebitmap_node_get_bit(node, i)) {
			int found = 0;
			unsigned j;
			for (j = 0; m[j] != -1; j++) {
				if (i != (unsigned)m[j])
					continue;
				found = 1;
				break;
			}
			if (found)
				continue;

			ret |= add_irule(src->s.value, i + 1, cls->s.value,
					 perm->s.value, effect, not, policy);
		}
	}

	return ret;
}

static int add_transition(char *srcS, char *origS, char *tgtS,
			  char *c, policydb_t *policy)
{
	int ret = 0;
	type_datum_t *src, *tgt, *orig;
	class_datum_t *cls;
	avtab_datum_t *av;
	avtab_key_t key;

	if (!(src = hashtab_search(policy->p_types.table, srcS))) {
		pr_err("Source type '%s' does not exist", srcS);
		ret = EINVAL;
	}
	if (!(orig = hashtab_search(policy->p_types.table, origS))) {
		pr_err("Origin type '%s' does not exist", origS);
		ret = EINVAL;
	}
	if (!(tgt = hashtab_search(policy->p_types.table, tgtS))) {
		pr_err("Target type '%s' does not exist", tgtS);
		ret = EINVAL;
	}
	if (!(cls = hashtab_search(policy->p_classes.table, c))) {
		pr_err("Class '%s' does not exist", c);
		ret = EINVAL;
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
			pr_err("Error inserting into avtab");
			return ret;
		}
	} else {
		pr_err("Warning, rule already defined! Won't override.");
		pr_err("Previous value = %d, wanted value = %d",
			av->data, tgt->s.value);
	}

	return ret;
}

static int add_file_transition(char *srcS, char *origS, char *tgtS,
			       char *c, const char* filename,
			       policydb_t *policy)
{
	int ret = 0;
	type_datum_t *src, *tgt, *orig;
	class_datum_t *cls;
	filename_trans_t *new_transition;

	if (!(src = hashtab_search(policy->p_types.table, srcS))) {
		pr_err("Source type '%s' does not exist", srcS);
		ret = EINVAL;
	}
	if (!(orig = hashtab_search(policy->p_types.table, origS))) {
		pr_err("Origin type '%s' does not exist", origS);
		ret = EINVAL;
	}
	if (!(tgt = hashtab_search(policy->p_types.table, tgtS))) {
		pr_err("Target type '%s' does not exist", tgtS);
		ret = EINVAL;
	}
	if (!(cls = hashtab_search(policy->p_classes.table, c))) {
		pr_err("Class '%s' does not exist", c);
		ret = EINVAL;
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

static int add_type(char *domainS, char *typeS, policydb_t *policy)
{
	int typeId;
	uint32_t i;
	type_datum_t *domain;
	class_datum_t *cl;
	constraint_node_t *n;
	constraint_expr_t *e;

	if (!(domain = hashtab_search(policy->p_types.table, domainS))) {
		pr_err("Domain '%s' does not exist", domainS);
		return EINVAL;
	}

	set_attr(typeS, domain->s.value, policy);

	if (!(typeId = get_attr_id(typeS, policy)))
		return EINVAL;

	/* Now let's update all constraints!
	  (kernel doesn't support (yet?) type_names rules) */
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

static void print_policy_info(policydb_t *p, FILE *fp)
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

static int load_policy(const char *filename,
		       policydb_t *policydb, struct policy_file *pf)
{
	off_t sz;
	void *map;

	int fd = open(filename, O_RDONLY);
	if (fd < 0) {
		pr_err("Can't open '%s': %s", filename, strerror(errno));
		return errno;
	}

	sz = lseek(fd, 0, SEEK_END);
	if (sz < 0) {
		pr_err("Can't get size of '%s': %s", filename, strerror(errno));
		close(fd);
		return errno;
	}
	lseek(fd, 0, SEEK_SET);

	map = mmap(NULL, sz, PROT_READ | PROT_WRITE, MAP_PRIVATE, fd, 0);

	close(fd);

	if (map == MAP_FAILED) {
		pr_err("Can't mmap '%s':  %s", filename, strerror(errno));
		return errno;
	}

	policy_file_init(pf);
	pf->type = PF_USE_MEMORY;
	pf->data = map;
	pf->len = sz;

	if (policydb_init(policydb)) {
		pr_err("policydb_init: Out of memory!");
		return ENOMEM;
	}

	if (policydb_read(policydb, pf, 0)) {
		pr_err("Error(s) encountered while parsing configuration");
		policydb_destroy(policydb);
		return EINVAL;
	}

	return 0;
}

static int apply_policy(policydb_t *policydb) {
	int fd, ret = 0;
	void *policy;
	size_t len;

	if ((ret = policydb_to_image(NULL, policydb, &policy, &len))) {
		pr_err("Could not convert policydb to image");
		return ret;
	}

	if ((fd = open(policy_load, O_WRONLY)) < 0) {
		pr_err("Could not open '%s' for writing: %s",
			policy_load, strerror(errno));
		return errno;
	}

	if (write(fd, policy, len) != (ssize_t)len) {
		pr_err("Could not write policy to '%s': %s",
			policy_load, strerror(errno));
		ret = errno;
	}

	close(fd);
	return ret;
}

static int write_policy_to_file(policydb_t *policydb, const char *filename) {
	int ret = 0;
	FILE *fp;
	struct policy_file pf;

	if (!(fp = fopen(filename, "w"))) {
		pr_err("Could not open file '%s' for writing: %s",
			filename, strerror(errno));
		return errno;
	}

	policy_file_init(&pf);
	pf.type = PF_USE_STDIO;
	pf.fp = fp;

	if ((ret = policydb_write(policydb, &pf)))
		pr_err("Could not write policy to file '%s'", filename);

	fclose(fp);
	return ret;
}

int main(int argc, char **argv)
{
	const char *policy = NULL, *outfile = NULL, *filetrans = NULL;
	char *source = NULL, *target = NULL,
		*class = NULL, *perm = NULL, *fcon = NULL,
		*permissive = NULL, *attr = NULL;
	int ch, ret = 0, info = 0, exists = 0, live = 0,
		not = 0, permissive_value = 0, noaudit = 0;
	sidtab_t sidtab;
	policydb_t policydb;
	struct policy_file pf;
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
		{"live", no_argument, NULL, 'L'},
		{"permissive", required_argument, NULL, 'Z'},
		{"not-permissive", required_argument, NULL, 'z'},
		{"not", no_argument, NULL, 0},
		{NULL, 0, NULL, 0}
	};

	int option_index = -1;
	while ((ch = getopt_long(argc, argv, "a:c:ef:g:s:t:p:P:o:L:Z:z:n",
				 long_options, &option_index)) != -1) {
		switch (ch) {
		case 0:
			if (!strcmp(long_options[option_index].name, "live")) {
				live = 1;
				break;
			}
			if (!strcmp(long_options[option_index].name, "not")) {
				not = 1;
				break;
			}
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
		case 'L':
			live = 1;
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

	if (!policy || (live && policy))
		/* we can only load one policy */
		usage(argv[0]);

	if (live)
		policy = policy_live;

	if (!source && !target && !class && !perm && !permissive && !fcon &&
	    !fcon && !attr && !filetrans && !exists && !noaudit && !outfile) {
		/* just load policy and show info if only -P or --live */
		info = 1;
	} else if (exists) {
		/* we can currently only check for existence of source/class */
		if (!source && !class)
			usage(argv[0]);
		/* abort on any invalid existence checks */
		if (permissive || source || target || class || perm ||
		    fcon || attr || filetrans || noaudit || outfile)
			usage(argv[0]);
	} else if (permissive) {
		/* abort on any invalid domain creation args */
		if (source || target || class || perm ||
		    fcon || attr || filetrans || noaudit)
			usage(argv[0]);
	} else if ((!source || !target || !class || !perm)
		   && !fcon && !attr && !filetrans) {
		/* not enough params to create a domain or rule */
		usage(argv[0]);
	}

	sepol_set_policydb(&policydb);
	sepol_set_sidtab(&sidtab);

	if ((ret = load_policy(policy, &policydb, &pf))) {
		pr_err("Could not load policy from '%s'", policy);
		return ret;
	}
	if ((ret = policydb_load_isids(&policydb, &sidtab))) {
		print_policy_info(&policydb, stderr);
		pr_err("Could not load policydb isids");
		goto exit;
	}

	printf("Loaded policy: ");
	print_policy_info(&policydb, stdout);

	if (info)
		goto exit;

	if (!outfile && !live)
		outfile = policy;

	if (exists) {
		if (source) {
			type_datum_t *tmp = hashtab_search(policydb.p_types.table, source);
			pr_info("Source type '%s' %s in the policy", source,
				tmp ? "exists" : "does not exist");
			ret |= !!tmp;
		}
		if (class) {
			class_datum_t *tmp = hashtab_search(policydb.p_classes.table, class);
			pr_info("Class '%s' %s in the policy", class,
				tmp ? "exists" : "does not exist");
			ret |= !!tmp;
		}
		goto exit;
	} else if (permissive) {
		type_datum_t *type;

		if (!(type = create_domain(permissive, &policydb))) {
			pr_err("Could not create domain '%s'", permissive);
			ret = 1;
			goto exit;
		}
		if ((ret = ebitmap_set_bit(&policydb.permissive_map,
					   type->s.value, permissive_value))) {
			pr_err("Could not set bit in permissive map");
			goto exit;
		}
		pr_info("Set permissive value of domain '%s' to %d",
			permissive, permissive_value);
	} else if (filetrans) {
		if ((ret = add_file_transition(source, fcon, target, class,
					       filetrans, &policydb))) {
			pr_err("Could not add file transition");
			goto exit;
		}
		pr_info("Added file transition ("
			"file name '%s', source type '%s', "
			"file context '%s', target type '%s', "
			"class '%s')",
			filetrans, source, fcon, target, class);
	} else if (fcon) {
		if ((ret = add_transition(source, fcon, target,
					  class, &policydb))) {
			pr_err("Could not add transition");
			goto exit;
		}
		pr_info("Added transition ("
			"source type '%s', file context '%s', "
			"target type '%s', class '%s')",
			source, fcon, target, class);
	} else if (attr) {
		if ((ret = add_type(source, attr, &policydb))) {
			pr_err("Could not add attr");
			goto exit;
		}
		pr_info("Added attr '%s' to source type '%s'", attr, source);
	} else if (noaudit) {
		if ((ret = add_rule(source, target, class, perm,
				    AVTAB_AUDITDENY, not, &policydb))) {
			pr_err("Could not add rule");
			goto exit;
		}
		pr_info("Added %s rule ("
			"source type '%s', target type '%s', "
			"class '%s', perm '%s')",
			not ? "audit" : "noaudit",
			source, target, class, perm);
	} else {
		/* add a rule to a whole set of typeattribute, not just a type */
		if (target && *target == '=') {
			char *saveptr = NULL, *m = NULL;
			char *vals[64];
			char *a = strtok_r(target, "-", &saveptr);
			int i = 0;

			while ((m = strtok_r(NULL, "-", &saveptr)))
				vals[i++] = m;
			vals[i] = NULL;

			if ((ret = add_typerule(source, a + 1, vals, class,
						perm, AVTAB_ALLOWED, not,
						&policydb))) {
				pr_err("Could not add type rule");
				goto exit;
			}
			pr_info("Added %s type rule ("
				"source type '%s', target type '%s', "
				"class '%s', perm '%s')",
				not ? "deny" : "allow",
				source, a + 1, class, perm);
		}
		if (perm) {
			char *saveptr = NULL;
			char *p = strtok_r(perm, ",", &saveptr);

			do {
				if ((ret = add_rule(source, target, class, p,
						    AVTAB_ALLOWED, not,
						    &policydb))) {
					pr_err("Could not add rule");
					goto exit;
				}
				pr_info("Added %s rule ("
					"source type '%s', target type '%s', "
					"class '%s', perm '%s')",
					not ? "deny" : "allow",
					source, target, class, p);
			} while ((p = strtok_r(NULL, ",", &saveptr)));
		} else {
			if ((ret = add_rule(source, target, class, NULL,
				     AVTAB_ALLOWED, not, &policydb))) {
				pr_err("Could not add rule");
				goto exit;
			}
			pr_info("Added %s rule ("
				"source type '%s', target type '%s', "
				"class '%s')",
				not ? "deny" : "allow",
				source, target, class);
		}
	}

	printf("New policy: ");
	print_policy_info(&policydb, stdout);

	if (outfile) {
		ret = write_policy_to_file(&policydb, outfile);
		goto exit;
	}

	if (live)
		ret = apply_policy(&policydb);

exit:
	policydb_destroy(&policydb);

	return ret;
}
