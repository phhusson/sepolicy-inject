/*
 * Copyright 2011 Tresys Technology, LLC. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 *    1. Redistributions of source code must retain the above copyright notice,
 *       this list of conditions and the following disclaimer.
 * 
 *    2. Redistributions in binary form must reproduce the above copyright notice,
 *       this list of conditions and the following disclaimer in the documentation
 *       and/or other materials provided with the distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY TRESYS TECHNOLOGY, LLC ``AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO
 * EVENT SHALL TRESYS TECHNOLOGY, LLC OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
 * OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * The views and conclusions contained in the software and documentation are those
 * of the authors and should not be interpreted as representing official policies,
 * either expressed or implied, of Tresys Technology, LLC.
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <sepol/policydb/conditional.h>

#include "cil_internal.h"
#include "cil_flavor.h"
#include "cil_log.h"
#include "cil_mem.h"
#include "cil_tree.h"
#include "cil_list.h"
#include "cil_build_ast.h"
#include "cil_resolve_ast.h"
#include "cil_reset_ast.h"
#include "cil_copy_ast.h"
#include "cil_verify.h"
#include "cil_strpool.h"

struct cil_args_resolve {
	struct cil_db *db;
	enum cil_pass pass;
	uint32_t *changed;
	struct cil_tree_node *callstack;
	struct cil_tree_node *optstack;
	struct cil_tree_node *boolif;
	struct cil_tree_node *macro;
	struct cil_list *sidorder_lists;
	struct cil_list *classorder_lists;
	struct cil_list *catorder_lists;
	struct cil_list *sensitivityorder_lists;
	struct cil_list *in_list;
};

static struct cil_name * __cil_insert_name(struct cil_db *db, hashtab_key_t key, struct cil_tree_node *ast_node)
{
	/* Currently only used for typetransition file names.
	   But could be used for any string that is passed as a parameter.
	*/
	struct cil_tree_node *parent = ast_node->parent;
	struct cil_macro *macro = NULL;
	struct cil_name *name;
	symtab_t *symtab;
	enum cil_sym_index sym_index;
	struct cil_symtab_datum *datum = NULL;

	cil_flavor_to_symtab_index(CIL_NAME, &sym_index);
	symtab = &((struct cil_root *)db->ast->root->data)->symtab[sym_index];

	cil_symtab_get_datum(symtab, key, &datum);
	if (datum != NULL) {
		return (struct cil_name *)datum;
	}

	if (parent->flavor == CIL_CALL) {
		struct cil_call *call = parent->data;
		macro = call->macro;	
	} else if (parent->flavor == CIL_MACRO) {
		macro = parent->data;
	}
	if (macro != NULL) {
		struct cil_list_item *item;
		cil_list_for_each(item, macro->params) {
			if (((struct cil_param*)item->data)->str == key) {
				return NULL;
			}
		}
	}

	cil_name_init(&name);
	cil_symtab_insert(symtab, key, (struct cil_symtab_datum *)name, ast_node);
	cil_list_append(db->names, CIL_NAME, name);

	return name;
}

static int __cil_resolve_perms(symtab_t *class_symtab, symtab_t *common_symtab, struct cil_list *perm_strs, struct cil_list **perm_datums)
{
	int rc = SEPOL_ERR;
	struct cil_list_item *curr;

	cil_list_init(perm_datums, perm_strs->flavor);

	cil_list_for_each(curr, perm_strs) {
		if (curr->flavor == CIL_LIST) {
			struct cil_list *sub_list;
			rc = __cil_resolve_perms(class_symtab, common_symtab, curr->data, &sub_list);
			if (rc != SEPOL_OK) {
				cil_log(CIL_ERR, "Failed to resolve permission list\n");
				goto exit;
			}
			cil_list_append(*perm_datums, CIL_LIST, sub_list);
		} else if (curr->flavor == CIL_STRING) {
			struct cil_symtab_datum *perm_datum = NULL;
			rc = cil_symtab_get_datum(class_symtab, curr->data, &perm_datum);
			if (rc == SEPOL_ENOENT) {
				if (common_symtab) {
					rc = cil_symtab_get_datum(common_symtab, curr->data, &perm_datum);
				}
			}
			if (rc != SEPOL_OK) {
				cil_log(CIL_ERR, "Failed to resolve permission %s\n", (char*)curr->data);
				goto exit;
			}
			cil_list_append(*perm_datums, CIL_DATUM, perm_datum);
		} else {
			cil_list_append(*perm_datums, curr->flavor, curr->data);
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_classperms(struct cil_tree_node *current, struct cil_classperms *cp, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_symtab_datum *datum = NULL;
	symtab_t *common_symtab = NULL;
	struct cil_class *class;

	rc = cil_resolve_name(current, cp->class_str, CIL_SYM_CLASSES, extra_args, &datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	class = (struct cil_class *)datum;

	if (class->common != NULL) {
		common_symtab = &class->common->perms;
	}

	cp->class = class;

	rc = __cil_resolve_perms(&class->perms, common_symtab, cp->perm_strs, &cp->perms);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_classperms_set(struct cil_tree_node *current, struct cil_classperms_set *cp_set, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_symtab_datum *datum = NULL;

	rc = cil_resolve_name(current, cp_set->set_str, CIL_SYM_CLASSPERMSETS, extra_args, &datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	cp_set->set = (struct cil_classpermission*)datum;

	/* This could be an anonymous classpermission */
	if (datum->name == NULL) {
		rc = cil_resolve_classperms_list(current, cp_set->set->classperms, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_classperms_list(struct cil_tree_node *current, struct cil_list *cp_list, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_list_item *curr;

	cil_list_for_each(curr, cp_list) {
		if (curr->flavor == CIL_CLASSPERMS) {
			rc = cil_resolve_classperms(current, curr->data, extra_args);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		} else {
			rc = cil_resolve_classperms_set(current, curr->data, extra_args);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_classpermissionset(struct cil_tree_node *current, struct cil_classpermissionset *cps, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_args_resolve *args = extra_args;
	struct cil_list_item *curr;
	struct cil_symtab_datum *datum;
	struct cil_classpermission *cp;

	rc = cil_resolve_name(current, cps->set_str, CIL_SYM_CLASSPERMSETS, args, &datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	rc = cil_resolve_classperms_list(current, cps->classperms, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	cp = (struct cil_classpermission *)datum;

	if (cp->classperms == NULL) {
		cil_list_init(&cp->classperms, CIL_CLASSPERMS);
	}

	cil_list_for_each(curr, cps->classperms) {
		cil_list_append(cp->classperms, curr->flavor, curr->data);
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_type_used(struct cil_symtab_datum *datum)
{
	struct cil_typeattribute *attr = NULL;

	if (FLAVOR(datum) == CIL_TYPEATTRIBUTE) {
		attr = (struct cil_typeattribute*)datum;
		attr->used = CIL_TRUE;
	}

	return 0;
}

int cil_resolve_avrule(struct cil_tree_node *current, void *extra_args)
{
	struct cil_args_resolve *args = extra_args;
	struct cil_db *db = NULL;

	struct cil_avrule *rule = current->data;
	struct cil_symtab_datum *src_datum = NULL;
	struct cil_symtab_datum *tgt_datum = NULL;
	int rc = SEPOL_ERR;

	if (args != NULL) {
		db = args->db;
	}

	rc = cil_resolve_name(current, rule->src_str, CIL_SYM_TYPES, args, &src_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	rule->src = src_datum;
	if (rule->rule_kind != CIL_AVRULE_NEVERALLOW) {
		cil_type_used(src_datum);
	}
		
	if (rule->tgt_str == CIL_KEY_SELF) {
		rule->tgt = db->selftype;
	} else {
		rc = cil_resolve_name(current, rule->tgt_str, CIL_SYM_TYPES, args, &tgt_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		rule->tgt = tgt_datum;
		if (rule->rule_kind != CIL_AVRULE_NEVERALLOW) {
			cil_type_used(tgt_datum);
		}
	}

	rc = cil_resolve_classperms_list(current, rule->classperms, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_type_rule(struct cil_tree_node *current, void *extra_args)
{
	struct cil_type_rule *rule = current->data;
	struct cil_symtab_datum *src_datum = NULL;
	struct cil_symtab_datum *tgt_datum = NULL;
	struct cil_symtab_datum *obj_datum = NULL;
	struct cil_symtab_datum *result_datum = NULL;
	struct cil_tree_node *result_node = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, rule->src_str, CIL_SYM_TYPES, extra_args, &src_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	rule->src = src_datum;
	cil_type_used(src_datum);

	rc = cil_resolve_name(current, rule->tgt_str, CIL_SYM_TYPES, extra_args, &tgt_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	rule->tgt = tgt_datum;
	cil_type_used(tgt_datum);

	rc = cil_resolve_name(current, rule->obj_str, CIL_SYM_CLASSES, extra_args, &obj_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	rule->obj = (struct cil_class*)obj_datum;

	rc = cil_resolve_name(current, rule->result_str, CIL_SYM_TYPES, extra_args, &result_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	result_node = result_datum->nodes->head->data;

	if (result_node->flavor != CIL_TYPE) {
		cil_log(CIL_ERR, "Type rule result must be a type [%d]\n",result_node->flavor);
		rc = SEPOL_ERR;
		goto exit;
	}
	rule->result = result_datum;

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_typeattributeset(struct cil_tree_node *current, void *extra_args)
{
	struct cil_typeattributeset *attrtypes = current->data;
	struct cil_symtab_datum *attr_datum = NULL;
	struct cil_tree_node *attr_node = NULL;
	struct cil_typeattribute *attr = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, attrtypes->attr_str, CIL_SYM_TYPES, extra_args, &attr_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	attr_node = attr_datum->nodes->head->data;

	if (attr_node->flavor != CIL_TYPEATTRIBUTE) {
		rc = SEPOL_ERR;
		cil_log(CIL_ERR, "Attribute type not an attribute\n");
		goto exit;
	}

	attr = (struct cil_typeattribute*)attr_datum;

	rc = cil_resolve_expr(CIL_TYPEATTRIBUTESET, attrtypes->str_expr, &attrtypes->datum_expr, current, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	rc = cil_verify_no_self_reference(attr_datum, attrtypes->datum_expr);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	if (attr->expr_list == NULL) {
		cil_list_init(&attr->expr_list, CIL_TYPEATTRIBUTE);
	}

	cil_list_append(attr->expr_list, CIL_LIST, attrtypes->datum_expr);

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_aliasactual(struct cil_tree_node *current, void *extra_args, enum cil_flavor flavor)
{
	int rc = SEPOL_ERR;
	enum cil_sym_index sym_index;
	struct cil_aliasactual *aliasactual = current->data;
	struct cil_symtab_datum *alias_datum = NULL;
	struct cil_symtab_datum *actual_datum = NULL;
	struct cil_alias *alias;

	rc = cil_flavor_to_symtab_index(flavor, &sym_index);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	rc = cil_resolve_name(current, aliasactual->alias_str, sym_index, extra_args, &alias_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	rc = cil_resolve_name(current, aliasactual->actual_str, sym_index, extra_args, &actual_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	alias = (struct cil_alias *)alias_datum;

	if (alias->actual != NULL) {
		cil_log(CIL_ERR, "Alias cannot bind more than one value\n");
		rc = SEPOL_ERR;
		goto exit;
	}

	alias->actual = actual_datum;

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_alias_to_actual(struct cil_tree_node *current, enum cil_flavor flavor)
{
	struct cil_alias *alias = current->data;
	struct cil_alias *a1 = current->data;
	struct cil_alias *a2 = current->data;
	struct cil_tree_node *a1_node = NULL;
	int steps = 0;
	int limit = 2;

	if (alias->actual == NULL) {
		cil_log(CIL_ERR, "Alias declared but not used at line %d of %s\n",current->line, current->path);
		return SEPOL_ERR;
	}

	a1_node = a1->datum.nodes->head->data;

	while (flavor != a1_node->flavor) {
		a1 = a1->actual;
		a1_node = a1->datum.nodes->head->data;
		steps += 1;

		if (a1 == a2) {
			cil_log(CIL_ERR, "Circular alias found: %s ", a1->datum.name);
			a1 = a1->actual;
			while (a1 != a2) {
				cil_log(CIL_ERR, "%s ", a1->datum.name);
				a1 = a1->actual;
			}
			cil_log(CIL_ERR,"\n");
			return SEPOL_ERR;
		}

		if (steps == limit) {
			steps = 0;
			limit *= 2;
			a2 = a1;
		}
	}

	alias->actual = a1;

	return SEPOL_OK;
}

int cil_resolve_typepermissive(struct cil_tree_node *current, void *extra_args)
{
	struct cil_typepermissive *typeperm = current->data;
	struct cil_symtab_datum *type_datum = NULL;
	struct cil_tree_node *type_node = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, typeperm->type_str, CIL_SYM_TYPES, extra_args, &type_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	type_node = type_datum->nodes->head->data;

	if (type_node->flavor != CIL_TYPE && type_node->flavor != CIL_TYPEALIAS) {
		cil_log(CIL_ERR, "Typepermissive must be a type or type alias\n");
		rc = SEPOL_ERR;
		goto exit;
	}

	typeperm->type = type_datum;

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_nametypetransition(struct cil_tree_node *current, void *extra_args)
{
	struct cil_args_resolve *args = extra_args;
	struct cil_nametypetransition *nametypetrans = current->data;
	struct cil_symtab_datum *src_datum = NULL;
	struct cil_symtab_datum *tgt_datum = NULL;
	struct cil_symtab_datum *obj_datum = NULL;
	struct cil_symtab_datum *name_datum = NULL;
	struct cil_symtab_datum *result_datum = NULL;
	struct cil_tree_node *result_node = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, nametypetrans->src_str, CIL_SYM_TYPES, extra_args, &src_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	nametypetrans->src = src_datum;
	cil_type_used(src_datum);

	rc = cil_resolve_name(current, nametypetrans->tgt_str, CIL_SYM_TYPES, extra_args, &tgt_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	nametypetrans->tgt = tgt_datum;
	cil_type_used(tgt_datum);

	rc = cil_resolve_name(current, nametypetrans->obj_str, CIL_SYM_CLASSES, extra_args, &obj_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	nametypetrans->obj = (struct cil_class*)obj_datum;

	nametypetrans->name = __cil_insert_name(args->db, nametypetrans->name_str, current);
	if (nametypetrans->name == NULL) {
		rc = cil_resolve_name(current, nametypetrans->name_str, CIL_SYM_NAMES, extra_args, &name_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		nametypetrans->name = (struct cil_name *)name_datum;
	}

	rc = cil_resolve_name(current, nametypetrans->result_str, CIL_SYM_TYPES, extra_args, &result_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	result_node = result_datum->nodes->head->data;

	if (result_node->flavor != CIL_TYPE && result_node->flavor != CIL_TYPEALIAS) {
		cil_log(CIL_ERR, "typetransition result is not a type or type alias\n");
		rc = SEPOL_ERR;
		goto exit;
	}
	nametypetrans->result = result_datum;

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_rangetransition(struct cil_tree_node *current, void *extra_args)
{
	struct cil_rangetransition *rangetrans = current->data;
	struct cil_symtab_datum *src_datum = NULL;
	struct cil_symtab_datum *exec_datum = NULL;
	struct cil_symtab_datum *obj_datum = NULL;
	struct cil_symtab_datum *range_datum = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, rangetrans->src_str, CIL_SYM_TYPES, extra_args, &src_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	rangetrans->src = src_datum;
	cil_type_used(src_datum);

	rc = cil_resolve_name(current, rangetrans->exec_str, CIL_SYM_TYPES, extra_args, &exec_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	rangetrans->exec = exec_datum;
	cil_type_used(exec_datum);

	rc = cil_resolve_name(current, rangetrans->obj_str, CIL_SYM_CLASSES, extra_args, &obj_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	rangetrans->obj = (struct cil_class*)obj_datum;

	if (rangetrans->range_str != NULL) {
		rc = cil_resolve_name(current, rangetrans->range_str, CIL_SYM_LEVELRANGES, extra_args, &range_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		rangetrans->range = (struct cil_levelrange*)range_datum;

		/* This could still be an anonymous levelrange even if range_str is set, if range_str is a param_str*/
		if (rangetrans->range->datum.name == NULL) {
			rc = cil_resolve_levelrange(current, rangetrans->range, extra_args);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
	} else {
		rc = cil_resolve_levelrange(current, rangetrans->range, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int __class_update_perm_values(__attribute__((unused)) hashtab_key_t k, hashtab_datum_t d, void *args)
{
	struct cil_perm *perm = (struct cil_perm *)d;

	perm->value += *((int *)args);

	return SEPOL_OK;
}

int cil_resolve_classcommon(struct cil_tree_node *current, void *extra_args)
{
	struct cil_class *class = NULL;
	struct cil_class *common = NULL;
	struct cil_classcommon *clscom = current->data;
	struct cil_symtab_datum *class_datum = NULL;
	struct cil_symtab_datum *common_datum = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, clscom->class_str, CIL_SYM_CLASSES, extra_args, &class_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	rc = cil_resolve_name(current, clscom->common_str, CIL_SYM_COMMONS, extra_args, &common_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	class = (struct cil_class *)class_datum;
	common = (struct cil_class *)common_datum;
	if (class->common != NULL) {
		cil_log(CIL_ERR, "class cannot be associeated with more than one common\n");
		rc = SEPOL_ERR;
		goto exit;
	}

	class->common = common;

	cil_symtab_map(&class->perms, __class_update_perm_values, &common->num_perms);

	class->num_perms += common->num_perms;

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_classmapping(struct cil_tree_node *current, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_classmapping *mapping = current->data;
	struct cil_class *map = NULL;
	struct cil_perm *mp = NULL;
	struct cil_symtab_datum *datum = NULL;
	struct cil_list_item *curr;

	rc = cil_resolve_name(current, mapping->map_class_str, CIL_SYM_CLASSES, extra_args, &datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	map = (struct cil_class*)datum;

	rc = cil_symtab_get_datum(&map->perms, mapping->map_perm_str, &datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	mp = (struct cil_perm*)datum;

	rc = cil_resolve_classperms_list(current, mapping->classperms, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	if (mp->classperms == NULL) {
		cil_list_init(&mp->classperms, CIL_CLASSPERMS);
	}

	cil_list_for_each(curr, mapping->classperms) {
		cil_list_append(mp->classperms, curr->flavor, curr->data);
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_userrole(struct cil_tree_node *current, void *extra_args)
{
	struct cil_userrole *userrole = current->data;
	struct cil_symtab_datum *user_datum = NULL;
	struct cil_symtab_datum *role_datum = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, userrole->user_str, CIL_SYM_USERS, extra_args, &user_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	userrole->user = (struct cil_user*)user_datum;

	rc = cil_resolve_name(current, userrole->role_str, CIL_SYM_ROLES, extra_args, &role_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	userrole->role = role_datum;

	if (userrole->user->roles == NULL) {
		cil_list_init(&userrole->user->roles, CIL_LIST_ITEM);
	}

	cil_list_append(userrole->user->roles, CIL_ROLE, userrole->role);

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_userlevel(struct cil_tree_node *current, void *extra_args)
{
	struct cil_userlevel *usrlvl = current->data;
	struct cil_symtab_datum *user_datum = NULL;
	struct cil_symtab_datum *lvl_datum = NULL;
	struct cil_user *user = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, usrlvl->user_str, CIL_SYM_USERS, extra_args, &user_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	user = (struct cil_user*)user_datum;

	if (usrlvl->level_str != NULL) {
		rc = cil_resolve_name(current, usrlvl->level_str, CIL_SYM_LEVELS, extra_args, &lvl_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		usrlvl->level = (struct cil_level*)lvl_datum;
		user->dftlevel = usrlvl->level;

		/* This could still be an anonymous level even if level_str is set, if level_str is a param_str*/
		if (user->dftlevel->datum.name == NULL) {
			rc = cil_resolve_level(current, user->dftlevel, extra_args);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
	} else if (usrlvl->level != NULL) {
		rc = cil_resolve_level(current, usrlvl->level, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		user->dftlevel = usrlvl->level;
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_userrange(struct cil_tree_node *current, void *extra_args)
{
	struct cil_userrange *userrange = current->data;
	struct cil_symtab_datum *user_datum = NULL;
	struct cil_symtab_datum *range_datum = NULL;
	struct cil_user *user = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, userrange->user_str, CIL_SYM_USERS, extra_args, &user_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	user = (struct cil_user*)user_datum;

	if (userrange->range_str != NULL) {
		rc = cil_resolve_name(current, userrange->range_str, CIL_SYM_LEVELRANGES, extra_args, &range_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		userrange->range = (struct cil_levelrange*)range_datum;
		user->range = userrange->range;

		/* This could still be an anonymous levelrange even if levelrange_str is set, if levelrange_str is a param_str*/
		if (user->range->datum.name == NULL) {
			rc = cil_resolve_levelrange(current, user->range, extra_args);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
	} else if (userrange->range != NULL) {
		rc = cil_resolve_levelrange(current, userrange->range, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		user->range = userrange->range;
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_userprefix(struct cil_tree_node *current, void *extra_args)
{
	struct cil_userprefix *userprefix = current->data;
	struct cil_symtab_datum *user_datum = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, userprefix->user_str, CIL_SYM_USERS, extra_args, &user_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	userprefix->user = (struct cil_user*)user_datum;

exit:
	return rc;
}

int cil_resolve_selinuxuser(struct cil_tree_node *current, void *extra_args)
{
	struct cil_selinuxuser *selinuxuser = current->data;
	struct cil_symtab_datum *user_datum = NULL;
	struct cil_symtab_datum *lvlrange_datum = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, selinuxuser->user_str, CIL_SYM_USERS, extra_args, &user_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	selinuxuser->user = (struct cil_user*)user_datum;

	if (selinuxuser->range_str != NULL) {
		rc = cil_resolve_name(current, selinuxuser->range_str, CIL_SYM_LEVELRANGES, extra_args, &lvlrange_datum);
		if (rc != SEPOL_OK) {
			cil_log(CIL_ERR, "Unable to resolve name: %s\n", selinuxuser->range_str);
			goto exit;
		}
		selinuxuser->range = (struct cil_levelrange*)lvlrange_datum;

		/* This could still be an anonymous levelrange even if range_str is set, if range_str is a param_str*/
		if (selinuxuser->range->datum.name == NULL) {
			rc = cil_resolve_levelrange(current, selinuxuser->range, extra_args);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
	} else if (selinuxuser->range != NULL) {
		rc = cil_resolve_levelrange(current, selinuxuser->range, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	rc = SEPOL_OK;
exit:
	return rc;
}

int cil_resolve_roletype(struct cil_tree_node *current, void *extra_args)
{
	struct cil_roletype *roletype = current->data;
	struct cil_symtab_datum *role_datum = NULL;
	struct cil_symtab_datum *type_datum = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, roletype->role_str, CIL_SYM_ROLES, extra_args, &role_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	roletype->role = (struct cil_role*)role_datum;

	rc = cil_resolve_name(current, roletype->type_str, CIL_SYM_TYPES, extra_args, &type_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	roletype->type = (struct cil_type*)type_datum;
	cil_type_used(type_datum);

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_roletransition(struct cil_tree_node *current, void *extra_args)
{
	struct cil_roletransition *roletrans = current->data;
	struct cil_symtab_datum *src_datum = NULL;
	struct cil_symtab_datum *tgt_datum = NULL;
	struct cil_symtab_datum *obj_datum = NULL;
	struct cil_symtab_datum *result_datum = NULL;
	struct cil_tree_node *node = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, roletrans->src_str, CIL_SYM_ROLES, extra_args, &src_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	roletrans->src = (struct cil_role*)src_datum;

	rc = cil_resolve_name(current, roletrans->tgt_str, CIL_SYM_TYPES, extra_args, &tgt_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	roletrans->tgt = tgt_datum;
	cil_type_used(tgt_datum);

	rc = cil_resolve_name(current, roletrans->obj_str, CIL_SYM_CLASSES, extra_args, &obj_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	roletrans->obj = (struct cil_class*)obj_datum;

	rc = cil_resolve_name(current, roletrans->result_str, CIL_SYM_ROLES, extra_args, &result_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	node = result_datum->nodes->head->data;
	if (node->flavor != CIL_ROLE) {
		rc = SEPOL_ERR;
		printf("%i\n", node->flavor);
		cil_log(CIL_ERR, "roletransition must result in a role, but %s is a %s\n", roletrans->result_str, cil_node_to_string(node));
		goto exit;
	}
	roletrans->result = (struct cil_role*)result_datum;

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_roleallow(struct cil_tree_node *current, void *extra_args)
{
	struct cil_roleallow *roleallow = current->data;
	struct cil_symtab_datum *src_datum = NULL;
	struct cil_symtab_datum *tgt_datum = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, roleallow->src_str, CIL_SYM_ROLES, extra_args, &src_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	roleallow->src = (struct cil_role*)src_datum;

	rc = cil_resolve_name(current, roleallow->tgt_str, CIL_SYM_ROLES, extra_args, &tgt_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	roleallow->tgt = (struct cil_role*)tgt_datum;

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_roleattributeset(struct cil_tree_node *current, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_roleattributeset *attrroles = current->data;
	struct cil_symtab_datum *attr_datum = NULL;
	struct cil_tree_node *attr_node = NULL;
	struct cil_roleattribute *attr = NULL;

	rc = cil_resolve_name(current, attrroles->attr_str, CIL_SYM_ROLES, extra_args, &attr_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	attr_node = attr_datum->nodes->head->data;

	if (attr_node->flavor != CIL_ROLEATTRIBUTE) {
		rc = SEPOL_ERR;
		cil_log(CIL_ERR, "Attribute role not an attribute\n");
		goto exit;
	}
	attr = (struct cil_roleattribute*)attr_datum;

	rc = cil_resolve_expr(CIL_ROLEATTRIBUTESET, attrroles->str_expr, &attrroles->datum_expr, current, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	rc = cil_verify_no_self_reference(attr_datum, attrroles->datum_expr);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	if (attr->expr_list == NULL) {
		cil_list_init(&attr->expr_list, CIL_ROLEATTRIBUTE);
	}

	cil_list_append(attr->expr_list, CIL_LIST, attrroles->datum_expr);

	return SEPOL_OK;

exit:
	return rc;
}

struct cil_ordered_list {
	int merged;
	struct cil_list *list;
	struct cil_tree_node *node;
};

void __cil_ordered_list_init(struct cil_ordered_list **ordered)
{
	*ordered = cil_malloc(sizeof(**ordered));

	(*ordered)->merged = CIL_FALSE;
	(*ordered)->list = NULL;
	(*ordered)->node = NULL;
}

void __cil_ordered_list_destroy(struct cil_ordered_list **ordered)
{
	cil_list_destroy(&(*ordered)->list, CIL_FALSE);
	(*ordered)->node = NULL;
	free(*ordered);
	*ordered = NULL;
}

void __cil_ordered_lists_destroy(struct cil_list **ordered_lists)
{
	struct cil_list_item *item = NULL;

	if (*ordered_lists == NULL) {
		return;
	}

	item = (*ordered_lists)->head;
	while (item != NULL) {
		struct cil_list_item *next = item->next;
		struct cil_ordered_list *ordered = item->data;
		__cil_ordered_list_destroy(&ordered);
		free(item);
		item = next;
	}
	free(*ordered_lists);
	*ordered_lists = NULL;
}

void __cil_ordered_lists_reset(struct cil_list **ordered_lists)
{
	__cil_ordered_lists_destroy(ordered_lists);
	cil_list_init(ordered_lists, CIL_LIST_ITEM);
}

struct cil_list_item *__cil_ordered_item_insert(struct cil_list *old, struct cil_list_item *curr, struct cil_list_item *item)
{
	if (item->flavor == CIL_SID) {
		struct cil_sid *sid = item->data;
		if (sid->ordered == CIL_TRUE) {
			cil_log(CIL_ERR, "SID %s has already been merged into the ordered list\n", sid->datum.name);
			return NULL;
		}
		sid->ordered = CIL_TRUE;
	} else if (item->flavor == CIL_CLASS) {
		struct cil_class *class = item->data;
		if (class->ordered == CIL_TRUE) {
			cil_log(CIL_ERR, "Class %s has already been merged into the ordered list\n", class->datum.name);
			return NULL;
		}
		class->ordered = CIL_TRUE;
	} else if (item->flavor == CIL_CAT) {
		struct cil_cat *cat = item->data;
		if (cat->ordered == CIL_TRUE) {
			cil_log(CIL_ERR, "Category %s has already been merged into the ordered list\n", cat->datum.name);
			return NULL;
		}
		cat->ordered = CIL_TRUE;
	} else if (item->flavor == CIL_SENS) {
		struct cil_sens *sens = item->data;
		if (sens->ordered == CIL_TRUE) {
			cil_log(CIL_ERR, "Sensitivity %s has already been merged into the ordered list\n", sens->datum.name);
			return NULL;
		}
		sens->ordered = CIL_TRUE;
	}

	return cil_list_insert(old, curr, item->flavor, item->data);
}

int __cil_ordered_list_insert(struct cil_list *old, struct cil_list_item *ocurr, struct cil_list_item *nstart, struct cil_list_item *nstop)
{
	struct cil_list_item *ncurr = NULL;

	for (ncurr = nstart; ncurr != nstop; ncurr = ncurr->next) {
		ocurr = __cil_ordered_item_insert(old, ocurr, ncurr);
		if (ocurr == NULL) {
			return SEPOL_ERR;
		}
	}
	return SEPOL_OK;
}

struct cil_list_item *__cil_ordered_find_match(struct cil_list_item *t, struct cil_list_item *i)
{
	while (i) {
		if (i->data == t->data) {
			return i;
		}
		i = i->next;
	}
	return NULL;
}

int __cil_ordered_lists_merge(struct cil_list *old, struct cil_list *new)
{
	struct cil_list_item *omatch = NULL;
	struct cil_list_item *ofirst = old->head;
	struct cil_list_item *ocurr = NULL;
	struct cil_list_item *oprev = NULL;
	struct cil_list_item *nmatch = NULL;
	struct cil_list_item *nfirst = new->head;
	struct cil_list_item *ncurr = NULL;
	int rc = SEPOL_ERR;

	if (nfirst == NULL) {
		return SEPOL_OK;
	}

	if (ofirst == NULL) {
		/* First list added */
		rc = __cil_ordered_list_insert(old, NULL, nfirst, NULL);
		return rc;
	}

	/* Find a match between the new list and the old one */
	for (nmatch = nfirst; nmatch; nmatch = nmatch->next) {
		omatch = __cil_ordered_find_match(nmatch, ofirst);
		if (omatch) {
			break;
		}
	}

	if (!nmatch) {
		/* List cannot be merged yet */
		return SEPOL_ERR;
	}

	if (nmatch != nfirst && omatch != ofirst) {
		/* Potential ordering conflict--try again later */
		return SEPOL_ERR;
	}

	if (nmatch != nfirst) {
		/* Prepend the beginning of the new list up to the first match to the old list */
		rc = __cil_ordered_list_insert(old, NULL, nfirst, nmatch);
		if (rc != SEPOL_OK) {
			return rc;
		}
	}

	/* In the overlapping protion, add items from the new list not in the old list */
	ncurr = nmatch->next;
	ocurr = omatch->next;
	oprev = omatch;
	while (ncurr && ocurr) {
		if (ncurr->data == ocurr->data) {
			oprev = ocurr;
			ocurr = ocurr->next;
			ncurr = ncurr->next;
		} else {
			/* Handle gap in old: old = (A C)  new = (A B C) */
			nmatch = __cil_ordered_find_match(ocurr, ncurr->next);
			if (nmatch) {
				rc = __cil_ordered_list_insert(old, oprev, ncurr, nmatch);
				if (rc != SEPOL_OK) {
					return rc;
				}
				oprev = ocurr;
				ocurr = ocurr->next;
				ncurr = nmatch->next;
				continue;
			}
			/* Handle gap in new: old = (A B C)  new = (A C) */
			omatch = __cil_ordered_find_match(ncurr, ocurr->next);
			if (omatch) {
				/* Nothing to insert, just skip */
				oprev = omatch;
				ocurr = omatch->next;
				ncurr = ncurr->next;
				continue;
			} else {
				return SEPOL_ERR;
			}
		}
	}

	if (ncurr) {
		/* Add the rest of the items from the new list */
		rc = __cil_ordered_list_insert(old, old->tail, ncurr, NULL);
		if (rc != SEPOL_OK) {
			return rc;
		}
	}

	return SEPOL_OK;
}

struct cil_list *__cil_ordered_lists_merge_all(struct cil_list **ordered_lists)
{
	struct cil_list *composite = NULL;
	struct cil_list_item *curr = NULL;
	int changed = CIL_TRUE;
	int waiting = 1;
	int rc = SEPOL_ERR;

	cil_list_init(&composite, CIL_LIST_ITEM);

	while (waiting && changed == CIL_TRUE) {
		changed = CIL_FALSE;
		waiting = 0;
		cil_list_for_each(curr, *ordered_lists) {
			struct cil_ordered_list *ordered_list = curr->data;
			if (ordered_list->merged == CIL_FALSE) {
				rc = __cil_ordered_lists_merge(composite, ordered_list->list);
				if (rc != SEPOL_OK) {
					/* Can't merge yet */
					waiting++;
				} else {
					ordered_list->merged = CIL_TRUE;
					changed = CIL_TRUE;
				}
			}
		}
		if (waiting > 0 && changed == CIL_FALSE) {
			cil_list_for_each(curr, *ordered_lists) {
				struct cil_ordered_list *ordered_list = curr->data;
				if (ordered_list->merged == CIL_FALSE) {
					cil_log(CIL_ERR, "Unable to merge ordered list at line %d of %s\n",ordered_list->node->line, ordered_list->node->path);
				}
			}
			goto exit;
		}
	}

	__cil_ordered_lists_destroy(ordered_lists);

	return composite;

exit:
	cil_list_destroy(&composite, CIL_FALSE);
	return NULL;
}

int cil_resolve_classorder(struct cil_tree_node *current, void *extra_args)
{
	struct cil_args_resolve *args = extra_args;
	struct cil_list *classorder_list = args->classorder_lists;
	struct cil_classorder *classorder = current->data;
	struct cil_list *new = NULL;
	struct cil_list_item *curr = NULL;
	struct cil_symtab_datum *datum = NULL;
	struct cil_ordered_list *ordered = NULL;
	int rc = SEPOL_ERR;

	cil_list_init(&new, CIL_CLASSORDER);

	cil_list_for_each(curr, classorder->class_list_str) {
		rc = cil_resolve_name(current, (char *)curr->data, CIL_SYM_CLASSES, extra_args, &datum);
		if (rc != SEPOL_OK) {
			cil_log(CIL_ERR, "Failed to resolve class %s in classorder\n", (char *)curr->data);
			goto exit;
		}
		cil_list_append(new, CIL_CLASS, datum);
	}

	__cil_ordered_list_init(&ordered);
	ordered->list = new;
	ordered->node = current;
	cil_list_append(classorder_list, CIL_CLASSORDER, ordered);

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_sidorder(struct cil_tree_node *current, void *extra_args)
{
	struct cil_args_resolve *args = extra_args;
	struct cil_list *sidorder_list = args->sidorder_lists;
	struct cil_sidorder *sidorder = current->data;
	struct cil_list *new = NULL;
	struct cil_list_item *curr = NULL;
	struct cil_symtab_datum *datum = NULL;
	struct cil_ordered_list *ordered = NULL;
	int rc = SEPOL_ERR;

	cil_list_init(&new, CIL_SIDORDER);

	cil_list_for_each(curr, sidorder->sid_list_str) {
		rc = cil_resolve_name(current, (char *)curr->data, CIL_SYM_SIDS, extra_args, &datum);
		if (rc != SEPOL_OK) {
			cil_log(CIL_ERR, "Failed to resolve sid %s in sidorder\n", (char *)curr->data);
			goto exit;
		}
		cil_list_append(new, CIL_SID, datum);
	}

	__cil_ordered_list_init(&ordered);
	ordered->list = new;
	ordered->node = current;
	cil_list_append(sidorder_list, CIL_SIDORDER, ordered);

	return SEPOL_OK;

exit:
	return rc;
}

void cil_set_cat_values(struct cil_list *ordered_cats, struct cil_db *db)
{
	struct cil_list_item *curr;
	int v = 0;

	cil_list_for_each(curr, ordered_cats) {
		struct cil_cat *cat = curr->data;
		cat->value = v;
		v++;
	}

	db->num_cats = v;
}

int cil_resolve_catorder(struct cil_tree_node *current, void *extra_args)
{
	struct cil_args_resolve *args = extra_args;
	struct cil_list *catorder_list = args->catorder_lists;
	struct cil_catorder *catorder = current->data;
	struct cil_list *new = NULL;
	struct cil_list_item *curr = NULL;
	struct cil_symtab_datum *cat_datum;
	struct cil_cat *cat = NULL;
	struct cil_ordered_list *ordered = NULL;
	int rc = SEPOL_ERR;

	cil_list_init(&new, CIL_CATORDER);

	cil_list_for_each(curr, catorder->cat_list_str) {
		struct cil_tree_node *node = NULL;
		rc = cil_resolve_name(current, (char *)curr->data, CIL_SYM_CATS, extra_args, &cat_datum);
		if (rc != SEPOL_OK) {
			cil_log(CIL_ERR, "Failed to resolve category %s in categoryorder\n", (char *)curr->data);
			goto exit;
		}
		node = cat_datum->nodes->head->data;
		if (node->flavor != CIL_CAT) {
			cil_log(CIL_ERR, "%s is not a category. Only categories are allowed in categoryorder statements\n", cat_datum->name);
			rc = SEPOL_ERR;
			goto exit;
		}
		cat = (struct cil_cat *)cat_datum;
		cil_list_append(new, CIL_CAT, cat);
	}

	__cil_ordered_list_init(&ordered);
	ordered->list = new;
	ordered->node = current;
	cil_list_append(catorder_list, CIL_CATORDER, ordered);

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_sensitivityorder(struct cil_tree_node *current, void *extra_args)
{
	struct cil_args_resolve *args = extra_args;
	struct cil_list *sensitivityorder_list = args->sensitivityorder_lists;
	struct cil_sensorder *sensorder = current->data;
	struct cil_list *new = NULL;
	struct cil_list_item *curr = NULL;
	struct cil_symtab_datum *datum = NULL;
	struct cil_ordered_list *ordered = NULL;
	int rc = SEPOL_ERR;

	cil_list_init(&new, CIL_LIST_ITEM);

	cil_list_for_each(curr, sensorder->sens_list_str) {
		rc = cil_resolve_name(current, (char *)curr->data, CIL_SYM_SENS, extra_args, &datum);
		if (rc != SEPOL_OK) {
			cil_log(CIL_ERR, "Failed to resolve sensitivty %s in sensitivityorder\n", (char *)curr->data);
			goto exit;
		}
		cil_list_append(new, CIL_SENS, datum);
	}

	__cil_ordered_list_init(&ordered);
	ordered->list = new;
	ordered->node = current;
	cil_list_append(sensitivityorder_list, CIL_SENSITIVITYORDER, ordered);

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_cats(struct cil_tree_node *current, struct cil_cats *cats, void *extra_args)
{
	int rc = SEPOL_ERR;

	rc = cil_resolve_expr(CIL_CATSET, cats->str_expr, &cats->datum_expr, current, extra_args);
	if (rc != SEPOL_OK) {
		cil_log(CIL_ERR,"Unable to resolve categories\n");
		goto exit;
	}
	
	return SEPOL_OK;

exit:
	return rc;
}


int cil_resolve_catset(struct cil_tree_node *current, struct cil_catset *catset, void *extra_args)
{
	int rc = SEPOL_ERR;

	rc = cil_resolve_cats(current, catset->cats, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	rc = cil_verify_no_self_reference((struct cil_symtab_datum *)catset, catset->cats->datum_expr);
	if (rc != SEPOL_OK) {
		cil_list_destroy(&catset->cats->datum_expr, CIL_FALSE);
		goto exit;
	}

exit:
	return rc;
}

int cil_resolve_senscat(struct cil_tree_node *current, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_senscat *senscat = current->data;
	struct cil_symtab_datum *sens_datum;
	struct cil_sens *sens = NULL;

	rc = cil_resolve_name(current, (char*)senscat->sens_str, CIL_SYM_SENS, extra_args, &sens_datum);
	if (rc != SEPOL_OK) {
		cil_log(CIL_ERR, "Failed to find sensitivity\n");
		goto exit;
	}

	rc = cil_resolve_cats(current, senscat->cats, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	sens = (struct cil_sens *)sens_datum;

	if (sens->cats_list == NULL ) {
		cil_list_init(&sens->cats_list, CIL_CAT);
	}

	cil_list_append(sens->cats_list, CIL_CAT, senscat->cats);

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_level(struct cil_tree_node *current, struct cil_level *level, void *extra_args)
{
	struct cil_symtab_datum *sens_datum = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, (char*)level->sens_str, CIL_SYM_SENS, extra_args, &sens_datum);
	if (rc != SEPOL_OK) {
		cil_log(CIL_ERR, "Failed to find sensitivity\n");
		goto exit;
	}

	level->sens = (struct cil_sens *)sens_datum;

	if (level->cats != NULL) {
		rc = cil_resolve_cats(current, level->cats, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_levelrange(struct cil_tree_node *current, struct cil_levelrange *lvlrange, void *extra_args)
{
	struct cil_symtab_datum *low_datum = NULL;
	struct cil_symtab_datum *high_datum = NULL;
	int rc = SEPOL_ERR;

	if (lvlrange->low_str != NULL) {
		rc = cil_resolve_name(current, lvlrange->low_str, CIL_SYM_LEVELS, extra_args, &low_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		lvlrange->low = (struct cil_level*)low_datum;

		/* This could still be an anonymous level even if low_str is set, if low_str is a param_str */
		if (lvlrange->low->datum.name == NULL) {
			rc = cil_resolve_level(current, lvlrange->low, extra_args);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
	} else if (lvlrange->low != NULL) {
		rc = cil_resolve_level(current, lvlrange->low, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	if (lvlrange->high_str != NULL) {
		rc = cil_resolve_name(current, lvlrange->high_str, CIL_SYM_LEVELS, extra_args, &high_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		lvlrange->high = (struct cil_level*)high_datum;

		/* This could still be an anonymous level even if high_str is set, if high_str is a param_str */
		if (lvlrange->high->datum.name == NULL) {
			rc = cil_resolve_level(current, lvlrange->high, extra_args);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
	} else if (lvlrange->high != NULL) {
		rc = cil_resolve_level(current, lvlrange->high, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_constrain(struct cil_tree_node *current, void *extra_args)
{
	struct cil_constrain *cons = current->data;
	int rc = SEPOL_ERR;

	rc = cil_resolve_classperms_list(current, cons->classperms, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	rc = cil_resolve_expr(CIL_CONSTRAIN, cons->str_expr, &cons->datum_expr, current, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_validatetrans(struct cil_tree_node *current, void *extra_args)
{
	struct cil_validatetrans *validtrans = current->data;
	struct cil_args_resolve *args = extra_args;
	struct cil_symtab_datum *class_datum = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, validtrans->class_str, CIL_SYM_CLASSES, args, &class_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	validtrans->class = (struct cil_class*)class_datum;

	rc = cil_resolve_expr(CIL_VALIDATETRANS, validtrans->str_expr, &validtrans->datum_expr, current, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_context(struct cil_tree_node *current, struct cil_context *context, void *extra_args)
{
	struct cil_symtab_datum *user_datum = NULL;
	struct cil_symtab_datum *role_datum = NULL;
	struct cil_symtab_datum *type_datum = NULL;
	struct cil_tree_node *type_node = NULL;
	struct cil_symtab_datum *lvlrange_datum = NULL;

	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, context->user_str, CIL_SYM_USERS, extra_args, &user_datum);
	if (rc != SEPOL_OK) {
		cil_log(CIL_ERR, "Unable to resolve name: %s\n", context->user_str);
		goto exit;
	}
	context->user = (struct cil_user*)user_datum;

	rc = cil_resolve_name(current, context->role_str, CIL_SYM_ROLES, extra_args, &role_datum);
	if (rc != SEPOL_OK) {
		cil_log(CIL_ERR, "Unable to resolve name: %s\n", context->role_str);
		goto exit;
	}
	context->role = (struct cil_role*)role_datum;

	rc = cil_resolve_name(current, context->type_str, CIL_SYM_TYPES, extra_args, &type_datum);
	if (rc != SEPOL_OK) {
		cil_log(CIL_ERR, "Unable to resolve name: %s\n", context->type_str);
		goto exit;
	}

	type_node = type_datum->nodes->head->data;

	if (type_node->flavor != CIL_TYPE && type_node->flavor != CIL_TYPEALIAS) {
		rc = SEPOL_ERR;
		cil_log(CIL_ERR, "Type not a type or type alias\n");
		goto exit;
	}
	context->type = type_datum;

	if (context->range_str != NULL) {
		rc = cil_resolve_name(current, context->range_str, CIL_SYM_LEVELRANGES, extra_args, &lvlrange_datum);
		if (rc != SEPOL_OK) {
			cil_log(CIL_ERR, "Unable to resolve name: %s\n", context->range_str);
			goto exit;
		}
		context->range = (struct cil_levelrange*)lvlrange_datum;

		/* This could still be an anonymous levelrange even if levelrange_str is set, if levelrange_str is a param_str*/
		if (context->range->datum.name == NULL) {
			rc = cil_resolve_levelrange(current, context->range, extra_args);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
	} else if (context->range != NULL) {
		rc = cil_resolve_levelrange(current, context->range, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_filecon(struct cil_tree_node *current, void *extra_args)
{
	struct cil_filecon *filecon = current->data;
	struct cil_symtab_datum *context_datum = NULL;
	int rc = SEPOL_ERR;

	if (filecon->context_str != NULL) {
		rc = cil_resolve_name(current, filecon->context_str, CIL_SYM_CONTEXTS, extra_args, &context_datum);
		if (rc != SEPOL_OK) {
			return rc;
		}
		filecon->context = (struct cil_context*)context_datum;
	} else if (filecon->context != NULL) {
		rc = cil_resolve_context(current, filecon->context, extra_args);
		if (rc != SEPOL_OK) {
			return rc;
		}
	}

	return SEPOL_OK;
}

int cil_resolve_portcon(struct cil_tree_node *current, void *extra_args)
{
	struct cil_portcon *portcon = current->data;
	struct cil_symtab_datum *context_datum = NULL;
	int rc = SEPOL_ERR;

	if (portcon->context_str != NULL) {
		rc = cil_resolve_name(current, portcon->context_str, CIL_SYM_CONTEXTS, extra_args, &context_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		portcon->context = (struct cil_context*)context_datum;
	} else {
		rc = cil_resolve_context(current, portcon->context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_genfscon(struct cil_tree_node *current, void *extra_args)
{
	struct cil_genfscon *genfscon = current->data;
	struct cil_symtab_datum *context_datum = NULL;
	int rc = SEPOL_ERR;

	if (genfscon->context_str != NULL) {
		rc = cil_resolve_name(current, genfscon->context_str, CIL_SYM_CONTEXTS, extra_args, &context_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		genfscon->context = (struct cil_context*)context_datum;
	} else {
		rc = cil_resolve_context(current, genfscon->context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_nodecon(struct cil_tree_node *current, void *extra_args)
{
	struct cil_nodecon *nodecon = current->data;
	struct cil_symtab_datum *addr_datum = NULL;
	struct cil_symtab_datum *mask_datum = NULL;
	struct cil_symtab_datum *context_datum = NULL;
	int rc = SEPOL_ERR;

	if (nodecon->addr_str != NULL) {
		rc = cil_resolve_name(current, nodecon->addr_str, CIL_SYM_IPADDRS, extra_args, &addr_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		nodecon->addr = (struct cil_ipaddr*)addr_datum;
	}

	if (nodecon->mask_str != NULL) {
		rc = cil_resolve_name(current, nodecon->mask_str, CIL_SYM_IPADDRS, extra_args, &mask_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		nodecon->mask = (struct cil_ipaddr*)mask_datum;
	}

	if (nodecon->context_str != NULL) {
		rc = cil_resolve_name(current, nodecon->context_str, CIL_SYM_CONTEXTS, extra_args, &context_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		nodecon->context = (struct cil_context*)context_datum;
	} else {
		rc = cil_resolve_context(current, nodecon->context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	if (nodecon->addr->family != nodecon->mask->family) {
		cil_log(CIL_ERR, "Nodecon ip address not in the same family\n");
		rc = SEPOL_ERR;
		goto exit;
	}


	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_netifcon(struct cil_tree_node *current, void *extra_args)
{
	struct cil_netifcon *netifcon = current->data;
	struct cil_symtab_datum *ifcon_datum = NULL;
	struct cil_symtab_datum *packcon_datum = NULL;

	int rc = SEPOL_ERR;

	if (netifcon->if_context_str != NULL) {
		rc = cil_resolve_name(current, netifcon->if_context_str, CIL_SYM_CONTEXTS, extra_args, &ifcon_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		netifcon->if_context = (struct cil_context*)ifcon_datum;
	} else {
		rc = cil_resolve_context(current, netifcon->if_context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	if (netifcon->packet_context_str != NULL) {
		rc = cil_resolve_name(current, netifcon->packet_context_str, CIL_SYM_CONTEXTS, extra_args, &packcon_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		netifcon->packet_context = (struct cil_context*)packcon_datum;
	} else {
		rc = cil_resolve_context(current, netifcon->packet_context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}
	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_pirqcon(struct cil_tree_node *current, void *extra_args)
{
	struct cil_pirqcon *pirqcon = current->data;
	struct cil_symtab_datum *context_datum = NULL;
	int rc = SEPOL_ERR;

	if (pirqcon->context_str != NULL) {
		rc = cil_resolve_name(current, pirqcon->context_str, CIL_SYM_CONTEXTS, extra_args, &context_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		pirqcon->context = (struct cil_context*)context_datum;
	} else {
		rc = cil_resolve_context(current, pirqcon->context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_iomemcon(struct cil_tree_node *current, void *extra_args)
{
	struct cil_iomemcon *iomemcon = current->data;
	struct cil_symtab_datum *context_datum = NULL;
	int rc = SEPOL_ERR;

	if (iomemcon->context_str != NULL) {
		rc = cil_resolve_name(current, iomemcon->context_str, CIL_SYM_CONTEXTS, extra_args, &context_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		iomemcon->context = (struct cil_context*)context_datum;
	} else {
		rc = cil_resolve_context(current, iomemcon->context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_ioportcon(struct cil_tree_node *current, void *extra_args)
{
	struct cil_ioportcon *ioportcon = current->data;
	struct cil_symtab_datum *context_datum = NULL;
	int rc = SEPOL_ERR;

	if (ioportcon->context_str != NULL) {
		rc = cil_resolve_name(current, ioportcon->context_str, CIL_SYM_CONTEXTS, extra_args, &context_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		ioportcon->context = (struct cil_context*)context_datum;
	} else {
		rc = cil_resolve_context(current, ioportcon->context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_pcidevicecon(struct cil_tree_node *current, void *extra_args)
{
	struct cil_pcidevicecon *pcidevicecon = current->data;
	struct cil_symtab_datum *context_datum = NULL;
	int rc = SEPOL_ERR;

	if (pcidevicecon->context_str != NULL) {
		rc = cil_resolve_name(current, pcidevicecon->context_str, CIL_SYM_CONTEXTS, extra_args, &context_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		pcidevicecon->context = (struct cil_context*)context_datum;
	} else {
		rc = cil_resolve_context(current, pcidevicecon->context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_fsuse(struct cil_tree_node *current, void *extra_args)
{
	struct cil_fsuse *fsuse = current->data;
	struct cil_symtab_datum *context_datum = NULL;
	int rc = SEPOL_ERR;

	if (fsuse->context_str != NULL) {
		rc = cil_resolve_name(current, fsuse->context_str, CIL_SYM_CONTEXTS, extra_args, &context_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		fsuse->context = (struct cil_context*)context_datum;
	} else {
		rc = cil_resolve_context(current, fsuse->context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_sidcontext(struct cil_tree_node *current, void *extra_args)
{
	struct cil_sidcontext *sidcon = current->data;
	struct cil_symtab_datum *sid_datum = NULL;
	struct cil_symtab_datum *context_datum = NULL;
	struct cil_sid *sid = NULL;

	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, sidcon->sid_str, CIL_SYM_SIDS, extra_args, &sid_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}
	sid = (struct cil_sid*)sid_datum;

	if (sidcon->context_str != NULL) {
		rc = cil_resolve_name(current, sidcon->context_str, CIL_SYM_CONTEXTS, extra_args, &context_datum);
		if (rc != SEPOL_OK) {
			goto exit;
		}
		sidcon->context = (struct cil_context*)context_datum;
	} else if (sidcon->context != NULL) {
		rc = cil_resolve_context(current, sidcon->context, extra_args);
		if (rc != SEPOL_OK) {
			goto exit;
		}
	}

	if (sid->context != NULL) {
		cil_log(CIL_ERR, "sid's cannot be associated with more than one context\n");
		rc = SEPOL_ERR;
		goto exit;
	}

	sid->context = sidcon->context;

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_blockinherit(struct cil_tree_node *current, void *extra_args)
{
	struct cil_blockinherit *inherit = current->data;
	struct cil_args_resolve *args = extra_args;
	struct cil_db *db = NULL;
	struct cil_symtab_datum *block_datum = NULL;
	struct cil_tree_node *block_node = NULL;
	int rc = SEPOL_ERR;

	if (args != NULL) {
		db = args->db;
	}

	rc = cil_resolve_name(current, inherit->block_str, CIL_SYM_BLOCKS, extra_args, &block_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	block_node = block_datum->nodes->head->data;

	rc = cil_copy_ast(db, block_node, current);
	if (rc != SEPOL_OK) {
		cil_log(CIL_ERR, "Failed to copy block, rc: %d\n", rc);
		goto exit;
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_blockabstract(struct cil_tree_node *current, void *extra_args)
{
	struct cil_blockabstract *abstract = current->data;
	struct cil_symtab_datum *block_datum = NULL;
	struct cil_tree_node *block_node = NULL;
	int rc = SEPOL_ERR;

	rc = cil_resolve_name(current, abstract->block_str, CIL_SYM_BLOCKS, extra_args, &block_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	block_node = block_datum->nodes->head->data;
	if (block_node->flavor != CIL_BLOCK) {
		cil_log(CIL_ERR, "Failed to resolve blockabstract to a block, rc: %d\n", rc);
		goto exit;
	}

	((struct cil_block*)block_datum)->is_abstract = CIL_TRUE;

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_in(struct cil_tree_node *current, void *extra_args)
{
	struct cil_in *in = current->data;
	struct cil_args_resolve *args = extra_args;
	struct cil_db *db = NULL;
	struct cil_symtab_datum *block_datum = NULL;
	struct cil_tree_node *block_node = NULL;
	int rc = SEPOL_ERR;

	if (args != NULL) {
		db = args->db;
	}

	rc = cil_resolve_name(current, in->block_str, CIL_SYM_BLOCKS, extra_args, &block_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	block_node = block_datum->nodes->head->data;

	rc = cil_copy_ast(db, current, block_node);
	if (rc != SEPOL_OK) {
		printf("Failed to copy in, rc: %d\n", rc);
		goto exit;
	}

	cil_tree_children_destroy(current);
	current->cl_head = NULL;
	current->cl_tail = NULL;

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_in_list(void *extra_args)
{
	struct cil_args_resolve *args = extra_args;
	struct cil_list *ins = args->in_list;
	struct cil_list_item *curr = NULL;
	struct cil_tree_node *node = NULL;
	struct cil_tree_node *last_failed_node = NULL;
	struct cil_in *in = NULL;
	struct cil_symtab_datum *block_datum = NULL;
	int resolved = 0;
	int unresolved = 0;
	int rc = SEPOL_ERR;

	do {
		resolved = 0;
		unresolved = 0;

		cil_list_for_each(curr, ins) {
			if (curr->flavor != CIL_NODE) {
				continue;
			}

			node = curr->data;
			in = node->data;

			rc = cil_resolve_name(node, in->block_str, CIL_SYM_BLOCKS, extra_args, &block_datum);
			if (rc != SEPOL_OK) {
				unresolved++;
				last_failed_node = node;
			} else {
				rc = cil_resolve_in(node, extra_args);
				if (rc != SEPOL_OK) {
					goto exit;
				}
				
				resolved++;
				curr->data = NULL;
				curr->flavor = CIL_NONE;
			}
		}

		if (unresolved > 0 && resolved == 0) {
			cil_log(CIL_ERR, "Failed to resolve in-statement on line %d of %s\n", last_failed_node->line, last_failed_node->path);
			rc = SEPOL_ERR;
			goto exit;
		}

	} while (unresolved > 0);

	rc = SEPOL_OK;

exit:
	return rc;
}


int cil_resolve_bounds(struct cil_tree_node *current, void *extra_args, enum cil_flavor flavor)
{
	int rc = SEPOL_ERR;
	struct cil_bounds *bounds = current->data;
	enum cil_sym_index index;
	struct cil_symtab_datum *parent_datum = NULL;
	struct cil_symtab_datum *child_datum = NULL;

	rc = cil_flavor_to_symtab_index(flavor, &index);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	rc = cil_resolve_name(current, bounds->parent_str, index, extra_args, &parent_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	rc = cil_resolve_name(current, bounds->child_str, index, extra_args, &child_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	switch (flavor) {
	case CIL_USER: {
		struct cil_user *user = (struct cil_user *)child_datum;

		if (user->bounds != NULL) {
			struct cil_tree_node *node = user->bounds->datum.nodes->head->data;
			cil_log(CIL_ERR, "User %s already bound by parent at line %u of %s\n", bounds->child_str, node->line, node->path);
			rc = SEPOL_ERR;
			goto exit;
		}

		user->bounds = (struct cil_user *)parent_datum;
		break;
	}
	case CIL_ROLE: {
		struct cil_role *role = (struct cil_role *)child_datum;

		if (role->bounds != NULL) {
			struct cil_tree_node *node = role->bounds->datum.nodes->head->data;
			cil_log(CIL_ERR, "Role %s already bound by parent at line %u of %s\n", bounds->child_str, node->line, node->path);
			rc = SEPOL_ERR;
			goto exit;
		}

		role->bounds = (struct cil_role *)parent_datum;
		break;
	}
	case CIL_TYPE: {
		struct cil_type *type = (struct cil_type *)child_datum;
		struct cil_tree_node *node = NULL;

		if (type->bounds != NULL) {
			node = ((struct cil_symtab_datum *)type->bounds)->nodes->head->data;
			cil_log(CIL_ERR, "Type %s already bound by parent at line %u of %s\n", bounds->child_str, node->line, node->path);
			cil_log(CIL_ERR, "Now being bound to parent %s at line %u of %s\n", bounds->parent_str, current->line, current->path);
			rc = SEPOL_ERR;
			goto exit;
		}

		node = parent_datum->nodes->head->data;
		if (node->flavor == CIL_TYPEATTRIBUTE) {
			cil_log(CIL_ERR, "Bounds parent %s is an attribute\n", bounds->parent_str);
			rc = SEPOL_ERR;
			goto exit;
		}

		node = child_datum->nodes->head->data;
		if (node->flavor == CIL_TYPEATTRIBUTE) {
			cil_log(CIL_ERR, "Bounds child %s is an attribute\n", bounds->child_str);
			rc = SEPOL_ERR;
			goto exit;
		}

		type->bounds = (struct cil_type *)parent_datum;
		break;
	}
	default:
		break;
	}

	return SEPOL_OK;

exit:
	cil_log(CIL_ERR, "Bad bounds statement at line %u of %s\n", current->line, current->path);
	return rc;
}

int cil_resolve_default(struct cil_tree_node *current, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_default *def = current->data;
	struct cil_list_item *curr;
	struct cil_symtab_datum *datum;

	cil_list_init(&def->class_datums, def->flavor);

	cil_list_for_each(curr, def->class_strs) {
		rc = cil_resolve_name(current, (char *)curr->data, CIL_SYM_CLASSES, extra_args, &datum);
		if (rc != SEPOL_OK) {
			cil_log(CIL_ERR, "Failed to resolve class %s in %s\n", (char *)curr->data, cil_node_to_string(current));
			goto exit;
		}
		cil_list_append(def->class_datums, CIL_CLASS, datum);
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_defaultrange(struct cil_tree_node *current, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_defaultrange *def = current->data;
	struct cil_list_item *curr;
	struct cil_symtab_datum *datum;

	cil_list_init(&def->class_datums, CIL_DEFAULTRANGE);

	cil_list_for_each(curr, def->class_strs) {
		rc = cil_resolve_name(current, (char *)curr->data, CIL_SYM_CLASSES, extra_args, &datum);
		if (rc != SEPOL_OK) {
			cil_log(CIL_ERR, "Failed to resolve class %s in defaultrange\n", (char *)curr->data);
			goto exit;
		}
		cil_list_append(def->class_datums, CIL_CLASS, datum);
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_call1(struct cil_tree_node *current, void *extra_args)
{
	struct cil_call *new_call = current->data;
	struct cil_args_resolve *args = extra_args;
	struct cil_db *db = NULL;
	struct cil_tree_node *macro_node = NULL;
	struct cil_symtab_datum *macro_datum = NULL;
	int rc = SEPOL_ERR;

	if (args != NULL) {
		db = args->db;
	}

	rc = cil_resolve_name(current, new_call->macro_str, CIL_SYM_BLOCKS, extra_args, &macro_datum);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	macro_node = macro_datum->nodes->head->data;

	if (macro_node->flavor != CIL_MACRO) {
		printf("Failed to resolve macro %s\n", new_call->macro_str);
		rc = SEPOL_ERR;
		goto exit;
	}
	new_call->macro = (struct cil_macro*)macro_datum;

	if (new_call->macro->params != NULL ) {

		struct cil_list_item *item;
		struct cil_args *new_arg = NULL;
		struct cil_tree_node *pc = NULL;

		if (new_call->args_tree == NULL) {
			cil_log(CIL_ERR, "Missing arguments (%s, line: %d)\n", current->path, current->line);
			rc = SEPOL_ERR;
			goto exit;
		}

		pc = new_call->args_tree->root->cl_head;

		cil_list_init(&new_call->args, CIL_LIST_ITEM);

		cil_list_for_each(item, new_call->macro->params) {
			enum cil_flavor flavor = ((struct cil_param*)item->data)->flavor;

			if (pc == NULL) {
				cil_log(CIL_ERR, "Missing arguments (%s, line: %d)\n", current->path, current->line);
				rc = SEPOL_ERR;
				goto exit;
			}
			if (item->flavor != CIL_PARAM) {
				rc = SEPOL_ERR;
				goto exit;
			}

			cil_args_init(&new_arg);

			switch (flavor) {
			case CIL_NAME: {
				struct cil_name *name;
				name = __cil_insert_name(args->db, pc->data, current);
				if (name != NULL) {
					new_arg->arg = (struct cil_symtab_datum *)name;
				} else {
					new_arg->arg_str = pc->data;
				}
			}
				break;
			case CIL_TYPE:
				new_arg->arg_str = pc->data;
				break;
			case CIL_ROLE:
				new_arg->arg_str = pc->data;
				break;
			case CIL_USER:
				new_arg->arg_str = pc->data;
				break;
			case CIL_SENS:
				new_arg->arg_str = pc->data;
				break;
			case CIL_CAT:
				new_arg->arg_str = pc->data;
				break;
			case CIL_BOOL:
				new_arg->arg_str = pc->data;
				break;
			case CIL_CATSET: {
				if (pc->cl_head != NULL) {
					struct cil_catset *catset = NULL;
					struct cil_tree_node *cat_node = NULL;
					cil_catset_init(&catset);
					rc = cil_fill_cats(pc, &catset->cats);
					if (rc != SEPOL_OK) {
						cil_destroy_catset(catset);
						goto exit;
					}
					cil_tree_node_init(&cat_node);
					cat_node->flavor = CIL_CATSET;
					cat_node->data = catset;
					cil_list_append(((struct cil_symtab_datum*)catset)->nodes,
									CIL_LIST_ITEM, cat_node);
					new_arg->arg = (struct cil_symtab_datum*)catset;
				} else {
					new_arg->arg_str = pc->data;
				}

				break;
			}
			case CIL_LEVEL: {
				if (pc->cl_head != NULL) {
					struct cil_level *level = NULL;
					struct cil_tree_node *lvl_node = NULL;
					cil_level_init(&level);

					rc = cil_fill_level(pc->cl_head, level);
					if (rc != SEPOL_OK) {
						cil_log(CIL_ERR, "Failed to create anonymous level, rc: %d\n", rc);
						cil_destroy_level(level);
						goto exit;
					}
					cil_tree_node_init(&lvl_node);
					lvl_node->flavor = CIL_LEVEL;
					lvl_node->data = level;
					cil_list_append(((struct cil_symtab_datum*)level)->nodes, 
									CIL_LIST_ITEM, lvl_node);
					new_arg->arg = (struct cil_symtab_datum*)level;
				} else {
					new_arg->arg_str = pc->data;
				}

				break;
			}
			case CIL_LEVELRANGE: {
				if (pc->cl_head != NULL) {
					struct cil_levelrange *range = NULL;
					struct cil_tree_node *range_node = NULL;
					cil_levelrange_init(&range);

					rc = cil_fill_levelrange(pc->cl_head, range);
					if (rc != SEPOL_OK) {
						cil_log(CIL_ERR, "Failed to create anonymous levelrange, rc: %d\n", rc);
						cil_destroy_levelrange(range);
						goto exit;
					}
					cil_tree_node_init(&range_node);
					range_node->flavor = CIL_LEVELRANGE;
					range_node->data = range;
					cil_list_append(((struct cil_symtab_datum*)range)->nodes, 
									CIL_LIST_ITEM, range_node);
					new_arg->arg = (struct cil_symtab_datum*)range;
				} else {
					new_arg->arg_str = pc->data;
				}

				break;
			}
			case CIL_IPADDR: {
				if (pc->cl_head != NULL) {
					struct cil_ipaddr *ipaddr = NULL;
					struct cil_tree_node *addr_node = NULL;
					cil_ipaddr_init(&ipaddr);

					rc = cil_fill_ipaddr(pc->cl_head, ipaddr);
					if (rc != SEPOL_OK) {
						cil_log(CIL_ERR, "Failed to create anonymous ip address, rc; %d\n", rc);
						cil_destroy_ipaddr(ipaddr);
						goto exit;
					}
					cil_tree_node_init(&addr_node);
					addr_node->flavor = CIL_IPADDR;
					addr_node->data = ipaddr;
					cil_list_append(((struct cil_symtab_datum*)ipaddr)->nodes,
									CIL_LIST_ITEM, addr_node);
					new_arg->arg = (struct cil_symtab_datum*)ipaddr;
				} else {
					new_arg->arg_str = pc->data;
				}

				break;
			}
			case CIL_CLASS:
				new_arg->arg_str = pc->data;
				break;
			case CIL_MAP_CLASS:
				new_arg->arg_str = pc->data;
				break;
			case CIL_CLASSPERMISSION: {
				if (pc->cl_head != NULL) {
					struct cil_classpermission *cp = NULL;
					struct cil_tree_node *cp_node = NULL;

					cil_classpermission_init(&cp);
					rc = cil_fill_classperms_list(pc, &cp->classperms);
					if (rc != SEPOL_OK) {
						cil_log(CIL_ERR, "Failed to create anonymous classpermission\n");
						cil_destroy_classpermission(cp);
						goto exit;
					}
					cil_tree_node_init(&cp_node);
					cp_node->flavor = CIL_CLASSPERMISSION;
					cp_node->data = cp;
					cil_list_append(cp->datum.nodes, CIL_LIST_ITEM, cp_node);
					new_arg->arg = (struct cil_symtab_datum*)cp;
				} else {
					new_arg->arg_str = pc->data;
				}
				break;
			}
			default:
				cil_log(CIL_ERR, "Unexpected flavor: %d\n", 
						(((struct cil_param*)item->data)->flavor));
				rc = SEPOL_ERR;
				goto exit;
			}
			new_arg->param_str = ((struct cil_param*)item->data)->str;
			new_arg->flavor = flavor;

			cil_list_append(new_call->args, CIL_ARGS, new_arg);

			pc = pc->next;
		}

		if (pc != NULL) {
			cil_log(CIL_ERR, "Unexpected arguments (%s, line: %d)\n", current->path, current->line);
			rc = SEPOL_ERR;
			goto exit;
		}
	} else if (new_call->args_tree != NULL) {
		cil_log(CIL_ERR, "Unexpected arguments (%s, line: %d)\n", current->path, current->line);
		rc = SEPOL_ERR;
		goto exit;
	}

	if (new_call->copied == 0) {
		new_call->copied = 1;
		rc = cil_copy_ast(db, macro_node, current);
		if (rc != SEPOL_OK) {
			cil_log(CIL_ERR, "Failed to copy macro, rc: %d\n", rc);
			goto exit;
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_call2(struct cil_tree_node *current, void *extra_args)
{
	struct cil_call *new_call = current->data;
	int rc = SEPOL_ERR;
	enum cil_sym_index sym_index = CIL_SYM_UNKNOWN;
	struct cil_list_item *item;

	if (new_call->args == NULL) {
		rc = SEPOL_OK;
		goto exit;
	}

	cil_list_for_each(item, new_call->args) {
		struct cil_args *arg = item->data;
		if (arg->arg == NULL && arg->arg_str == NULL) {
			cil_log(CIL_ERR, "Arguments not created correctly\n");
			rc = SEPOL_ERR;
			goto exit;
		}

		switch (arg->flavor) {
		case CIL_NAME:
			if (arg->arg != NULL) {
				continue; /* No need to resolve */
			} else {
				sym_index = CIL_SYM_NAMES;
			}
			break;
		case CIL_LEVEL:
			if (arg->arg_str == NULL && arg->arg != NULL) {
				continue; // anonymous, no need to resolve
			} else {
				sym_index = CIL_SYM_LEVELS;
			}
			break;
		case CIL_LEVELRANGE:
			if (arg->arg_str == NULL && arg->arg != NULL) {
				continue; // anonymous, no need to resolve
			} else {
				sym_index = CIL_SYM_LEVELRANGES;
			}
			break;
		case CIL_CATSET:
			if (arg->arg_str == NULL && arg->arg != NULL) {
				continue; // anonymous, no need to resolve
			} else {
				sym_index = CIL_SYM_CATS;
			}
			break;
		case CIL_IPADDR:
			if (arg->arg_str == NULL && arg->arg != NULL) {
				continue; // anonymous, no need to resolve
			} else {
				sym_index = CIL_SYM_IPADDRS;
			}
			break;
		case CIL_CLASSPERMISSION:
			if (arg->arg_str == NULL && arg->arg != NULL) {
				continue;
			} else {
				sym_index = CIL_SYM_CLASSPERMSETS;
			}
			break;
		case CIL_TYPE:
			if (arg->arg_str == NULL && arg->arg != NULL) {
				continue; // anonymous, no need to resolve
			} else {
				sym_index = CIL_SYM_TYPES;
			}
			break;
		case CIL_ROLE:
			sym_index = CIL_SYM_ROLES;
			break;
		case CIL_USER:
			sym_index = CIL_SYM_USERS;
			break;
		case CIL_SENS:
			sym_index = CIL_SYM_SENS;
			break;
		case CIL_CAT:
			sym_index = CIL_SYM_CATS;
			break;
		case CIL_CLASS:
		case CIL_MAP_CLASS:
			sym_index = CIL_SYM_CLASSES;
			break;
		case CIL_BOOL:
			sym_index = CIL_SYM_BOOLS;
			break;
		default:
			rc = SEPOL_ERR;
			goto exit;
		}

		if (sym_index != CIL_SYM_UNKNOWN) {
			rc = cil_resolve_name(current, arg->arg_str, sym_index, extra_args, &(arg->arg));
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_name_call_args(struct cil_call *call, char *name, enum cil_sym_index sym_index, struct cil_symtab_datum **datum)
{
	struct cil_list_item *item;
	enum cil_sym_index param_index = CIL_SYM_UNKNOWN;
	int rc = SEPOL_ERR;

	if (call == NULL || name == NULL) {
		goto exit;
	}

	if (call->args == NULL) {
		goto exit;
	}

	cil_list_for_each(item, call->args) {
		struct cil_args * arg = item->data;
		rc = cil_flavor_to_symtab_index(arg->flavor, &param_index);
		if (param_index == sym_index) {
			if (name == arg->param_str) {
				*datum = arg->arg;
				rc = SEPOL_OK;
				goto exit;
			}
		}
	}

	return SEPOL_ERR;

exit:
	return rc;
}

int cil_resolve_expr(enum cil_flavor expr_type, struct cil_list *str_expr, struct cil_list **datum_expr, struct cil_tree_node *parent, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_list_item *curr;
	struct cil_symtab_datum *res_datum = NULL;
	enum cil_sym_index sym_index =  CIL_SYM_UNKNOWN;

	switch (str_expr->flavor) {
	case CIL_BOOL:
		sym_index = CIL_SYM_BOOLS;
		break;
	case CIL_TUNABLE:
		sym_index = CIL_SYM_TUNABLES;
		break;
	case CIL_TYPE:
		sym_index = CIL_SYM_TYPES;
		break;
	case CIL_ROLE:
		sym_index = CIL_SYM_ROLES;
		break;
	case CIL_USER:
		sym_index = CIL_SYM_USERS;
		break;
	case CIL_CAT:
		sym_index = CIL_SYM_CATS;
		break;
	default:
		break;
	}

	cil_list_init(datum_expr, str_expr->flavor);

	cil_list_for_each(curr, str_expr) {
		switch (curr->flavor) {
		case CIL_STRING:
			rc = cil_resolve_name(parent, curr->data, sym_index, extra_args, &res_datum);
			if (rc != SEPOL_OK) {
				goto exit;
			}

			if (sym_index == CIL_SYM_TYPES && (expr_type == CIL_CONSTRAIN || expr_type == CIL_VALIDATETRANS)) {
				cil_type_used(res_datum);
			}

			cil_list_append(*datum_expr, CIL_DATUM, res_datum);
			break;
		case CIL_LIST: {
			struct cil_list *datum_sub_expr;
			rc = cil_resolve_expr(expr_type, curr->data, &datum_sub_expr, parent, extra_args);
			if (rc != SEPOL_OK) {
				cil_list_destroy(&datum_sub_expr, CIL_TRUE);
				goto exit;
			}
			cil_list_append(*datum_expr, CIL_LIST, datum_sub_expr);
			break;
		}
		default:
			cil_list_append(*datum_expr, curr->flavor, curr->data);
			break;
		}				
	}
	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_boolif(struct cil_tree_node *current, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_booleanif *bif = (struct cil_booleanif*)current->data;

	rc = cil_resolve_expr(CIL_BOOLEANIF, bif->str_expr, &bif->datum_expr, current, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	return SEPOL_OK;

exit:
	return rc;
}

static int __cil_evaluate_tunable_expr(struct cil_list_item *curr);

static int __cil_evaluate_tunable_expr_helper(struct cil_list_item *curr)
{
	if (curr == NULL) {
		return CIL_FALSE;
	} else if (curr->flavor == CIL_DATUM) {
		struct cil_tunable *tun = curr->data;
		return tun->value;
	} else if (curr->flavor == CIL_LIST) {
		struct cil_list *l = curr->data;
		return __cil_evaluate_tunable_expr(l->head);
	} else {
		return CIL_FALSE;
	}
}

static int __cil_evaluate_tunable_expr(struct cil_list_item *curr)
{
	/* Assumes expression is well-formed */

	if (curr == NULL) {
		return CIL_FALSE;
	} else if (curr->flavor == CIL_OP) {
		uint16_t v1, v2;
		enum cil_flavor op_flavor = (enum cil_flavor)curr->data;

		v1 = __cil_evaluate_tunable_expr_helper(curr->next);

		if (op_flavor == CIL_NOT) return !v1;

		v2 = __cil_evaluate_tunable_expr_helper(curr->next->next);

		if (op_flavor == CIL_AND) return (v1 && v2);
		else if (op_flavor == CIL_OR) return (v1 || v2);
		else if (op_flavor == CIL_XOR) return (v1 ^ v2);
		else if (op_flavor == CIL_EQ) return (v1 == v2);
		else if (op_flavor == CIL_NEQ) return (v1 != v2);
		else return CIL_FALSE;
	} else {
		uint16_t v;
		for (;curr; curr = curr->next) {
			v = __cil_evaluate_tunable_expr_helper(curr);
			if (v) return v;
		}
		return CIL_FALSE;
	}
}

int cil_resolve_tunif(struct cil_tree_node *current, void *extra_args)
{
	struct cil_args_resolve *args = extra_args;
	struct cil_db *db = NULL;
	int rc = SEPOL_ERR;
	struct cil_tunableif *tif = (struct cil_tunableif*)current->data;
	uint16_t result = CIL_FALSE;
	struct cil_tree_node *true_node = NULL;
	struct cil_tree_node *false_node = NULL;
	struct cil_condblock *cb = NULL;

	if (args != NULL) {
		db = args->db;
	}

	rc = cil_resolve_expr(CIL_TUNABLEIF, tif->str_expr, &tif->datum_expr, current, extra_args);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	result = __cil_evaluate_tunable_expr(tif->datum_expr->head);

	if (current->cl_head != NULL && current->cl_head->flavor == CIL_CONDBLOCK) {
		cb = current->cl_head->data;
		if (cb->flavor == CIL_CONDTRUE) {
			true_node = current->cl_head;
		} else if (cb->flavor == CIL_CONDFALSE) {
			false_node = current->cl_head;
		}
	}

	if (current->cl_head != NULL && current->cl_head->next != NULL && current->cl_head->next->flavor == CIL_CONDBLOCK) {
		cb = current->cl_head->next->data;
		if (cb->flavor == CIL_CONDTRUE) {
			true_node = current->cl_head->next;
		} else if (cb->flavor == CIL_CONDFALSE) {
			false_node = current->cl_head->next;
		}
	}

	if (result == CIL_TRUE) {
		if (true_node != NULL) {
			rc = cil_copy_ast(db, true_node, current->parent);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
	} else {
		if (false_node != NULL) {
			rc = cil_copy_ast(db, false_node, current->parent);
			if (rc  != SEPOL_OK) {
				goto exit;
			}
		}
	}

	cil_tree_children_destroy(current);
	current->cl_head = NULL;
	current->cl_tail = NULL;

	return SEPOL_OK;

exit:
	return rc;
}


int __cil_resolve_ast_node(struct cil_tree_node *node, void *extra_args)
{
	int rc = SEPOL_OK;
	struct cil_args_resolve *args = extra_args;
	enum cil_pass pass = 0;
	struct cil_list *ins = args->in_list;

	if (node == NULL || args == NULL) {
		goto exit;
	}

	pass = args->pass;
	switch (pass) {
	case CIL_PASS_TIF:
		if (node->flavor == CIL_TUNABLEIF) {
			rc = cil_resolve_tunif(node, args);
		}
		break;
	case CIL_PASS_IN:
		if (node->flavor == CIL_IN) {
			// due to ordering issues, in statements are just gathered here and
			// resolved together in cil_resolve_in_list once all are found
			cil_list_prepend(ins, CIL_NODE, node);
		}
		break;
	case CIL_PASS_BLKIN:
		if (node->flavor == CIL_BLOCKINHERIT) {
			rc = cil_resolve_blockinherit(node, args);
		}
		break;
	case CIL_PASS_BLKABS:
		if (node->flavor == CIL_BLOCKABSTRACT) {
			rc = cil_resolve_blockabstract(node, args);
		}
		break;
	case CIL_PASS_MACRO:
		if (node->flavor == CIL_CALL && args->macro != NULL) {
			rc = cil_resolve_call1(node, args);
		}
		break;
	case CIL_PASS_CALL1:
		if (node->flavor == CIL_CALL) {
			rc = cil_resolve_call1(node, args);
		}
		break;
	case CIL_PASS_CALL2:
		if (node->flavor == CIL_CALL) {
			rc = cil_resolve_call2(node, args);
		}
		break;
	case CIL_PASS_ALIAS1:
		switch (node->flavor) {
		case CIL_TYPEALIASACTUAL:
			rc = cil_resolve_aliasactual(node, args, CIL_TYPE);
			break;
		case CIL_SENSALIASACTUAL:
			rc = cil_resolve_aliasactual(node, args, CIL_SENS);
			break;
		case CIL_CATALIASACTUAL:
			rc = cil_resolve_aliasactual(node, args, CIL_CAT);
			break;
		default: 
			break;
		}
		break;
	case CIL_PASS_ALIAS2:
		switch (node->flavor) {
		case CIL_TYPEALIAS:
			rc = cil_resolve_alias_to_actual(node, CIL_TYPE);
			break;
		case CIL_SENSALIAS:
			rc = cil_resolve_alias_to_actual(node, CIL_SENS);
			break;
		case CIL_CATALIAS:
			rc = cil_resolve_alias_to_actual(node, CIL_CAT);
			break;
		default:
			break;
		}
		break;
	case CIL_PASS_MISC1:
		switch (node->flavor) {
		case CIL_SIDORDER:
			rc = cil_resolve_sidorder(node, args);
			break;
		case CIL_CLASSORDER:
			rc = cil_resolve_classorder(node, args);
			break;
		case CIL_CATORDER:
			rc = cil_resolve_catorder(node, args);
			break;
		case CIL_SENSITIVITYORDER:
			rc = cil_resolve_sensitivityorder(node, args);
			break;
		case CIL_BOOLEANIF:
			rc = cil_resolve_boolif(node, args);
			break;
		default:
			break;
		}
		break;
	case CIL_PASS_MLS:
		switch (node->flavor) {
		case CIL_CATSET:
			rc = cil_resolve_catset(node, (struct cil_catset*)node->data, args);
			break;
		default:
			break;
		}
		break;
	case CIL_PASS_MISC2:
		switch (node->flavor) {
		case CIL_SENSCAT:
			rc = cil_resolve_senscat(node, args);
			break;
		case CIL_CLASSCOMMON:
			rc = cil_resolve_classcommon(node, args);
			break;
		default:
			break;
		}
		break;
	case CIL_PASS_MISC3:
		switch (node->flavor) {
		case CIL_TYPEATTRIBUTESET:
			rc = cil_resolve_typeattributeset(node, args);
			break;
		case CIL_TYPEBOUNDS:
			rc = cil_resolve_bounds(node, args, CIL_TYPE);
			break;
		case CIL_TYPEPERMISSIVE:
			rc = cil_resolve_typepermissive(node, args);
			break;
		case CIL_NAMETYPETRANSITION:
			rc = cil_resolve_nametypetransition(node, args);
			break;
		case CIL_RANGETRANSITION:
			rc = cil_resolve_rangetransition(node, args);
			break;
		case CIL_CLASSPERMISSIONSET:
			rc = cil_resolve_classpermissionset(node, (struct cil_classpermissionset*)node->data, args);
			break;
		case CIL_CLASSMAPPING:
			rc = cil_resolve_classmapping(node, args);
			break;
		case CIL_AVRULE:
			rc = cil_resolve_avrule(node, args);
			break;
		case CIL_TYPE_RULE:
			rc = cil_resolve_type_rule(node, args);
			break;
		case CIL_USERROLE:
			rc = cil_resolve_userrole(node, args);
			break;
		case CIL_USERLEVEL:
			rc = cil_resolve_userlevel(node, args);
			break;
		case CIL_USERRANGE:
			rc = cil_resolve_userrange(node, args);
			break;
		case CIL_USERBOUNDS:
			rc = cil_resolve_bounds(node, args, CIL_USER);
			break;
		case CIL_USERPREFIX:
			rc = cil_resolve_userprefix(node, args);
			break;
		case CIL_SELINUXUSER:
		case CIL_SELINUXUSERDEFAULT:
			rc = cil_resolve_selinuxuser(node, args);
			break;
		case CIL_ROLEATTRIBUTESET:
			rc = cil_resolve_roleattributeset(node, args);
			break;
		case CIL_ROLETYPE:
			rc = cil_resolve_roletype(node, args);
			break;
		case CIL_ROLETRANSITION:
			rc = cil_resolve_roletransition(node, args);
			break;
		case CIL_ROLEALLOW:
			rc = cil_resolve_roleallow(node, args);
			break;
		case CIL_ROLEBOUNDS:
			rc = cil_resolve_bounds(node, args, CIL_ROLE);
			break;
		case CIL_LEVEL:
			rc = cil_resolve_level(node, (struct cil_level*)node->data, args);
			break;
		case CIL_LEVELRANGE:
			rc = cil_resolve_levelrange(node, (struct cil_levelrange*)node->data, args);
			break;
		case CIL_CONSTRAIN:
			rc = cil_resolve_constrain(node, args);
			break;
		case CIL_MLSCONSTRAIN:
			rc = cil_resolve_constrain(node, args);
			break;
		case CIL_VALIDATETRANS:
		case CIL_MLSVALIDATETRANS:
			rc = cil_resolve_validatetrans(node, args);
			break;
		case CIL_CONTEXT:
			rc = cil_resolve_context(node, (struct cil_context*)node->data, args);
			break;
		case CIL_FILECON:
			rc = cil_resolve_filecon(node, args);
			break;
		case CIL_PORTCON:
			rc = cil_resolve_portcon(node, args);
			break;
		case CIL_NODECON:
			rc = cil_resolve_nodecon(node, args);
			break;
		case CIL_GENFSCON:
			rc = cil_resolve_genfscon(node, args);
			break;
		case CIL_NETIFCON:
			rc = cil_resolve_netifcon(node, args);
			break;
		case CIL_PIRQCON:
			rc = cil_resolve_pirqcon(node, args);
			break;
		case CIL_IOMEMCON:
			rc = cil_resolve_iomemcon(node, args);
			break;
		case CIL_IOPORTCON:
			rc = cil_resolve_ioportcon(node, args);
			break;
		case CIL_PCIDEVICECON:
			rc = cil_resolve_pcidevicecon(node, args);
			break;
		case CIL_FSUSE:
			rc = cil_resolve_fsuse(node, args);
			break;
		case CIL_SIDCONTEXT:
			rc = cil_resolve_sidcontext(node, args);
			break;
		case CIL_DEFAULTUSER:
		case CIL_DEFAULTROLE:
		case CIL_DEFAULTTYPE:
			rc = cil_resolve_default(node, args);
			break;
		case CIL_DEFAULTRANGE:
			rc = cil_resolve_defaultrange(node, args);
			break;
		default:
			break;
		}
		break;
	default:
		break;
	}

	return rc;

exit:
	return rc;
}

int __cil_resolve_ast_node_helper(struct cil_tree_node *node, __attribute__((unused)) uint32_t *finished, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_args_resolve *args = extra_args;
	enum cil_pass pass = args->pass;
	struct cil_tree_node *optstack = args->optstack;
	struct cil_tree_node *boolif = args->boolif;

	if (node == NULL) {
		goto exit;
	}

	if (optstack != NULL) {
		if (node->flavor == CIL_TUNABLE || node->flavor == CIL_MACRO) {
			/* tuanbles and macros are not allowed in optionals*/
			cil_log(CIL_ERR, "%s statement is not allowed in optionals (%s:%d)\n", cil_node_to_string(node), node->path, node->line);
			rc = SEPOL_ERR;
			goto exit;
		}
	}

	if (boolif != NULL) {
		if (!(node->flavor == CIL_CONDBLOCK ||
			node->flavor == CIL_AVRULE ||
			node->flavor == CIL_TYPE_RULE ||
			node->flavor == CIL_CALL ||
			node->flavor == CIL_TUNABLEIF ||
			node->flavor == CIL_NAMETYPETRANSITION)) {
			if (((struct cil_booleanif*)boolif->data)->preserved_tunable) {
				cil_log(CIL_ERR, "%s statement is not allowed in booleanifs (tunableif treated as a booleanif) (%s:%d)\n", cil_node_to_string(node), node->path, node->line);
			} else {
				cil_log(CIL_ERR, "%s statement is not allowed in booleanifs (%s:%d)\n", cil_node_to_string(node), node->path, node->line);
			}
			rc = SEPOL_ERR;
			goto exit;
		}
	}

	if (node->flavor == CIL_MACRO) {
		if (pass != CIL_PASS_TIF && pass != CIL_PASS_MACRO) {
			*finished = CIL_TREE_SKIP_HEAD;
			rc = SEPOL_OK;
			goto exit;
		}
	}

	if (node->flavor == CIL_OPTIONAL && ((struct cil_symtab_datum *)node->data)->state == CIL_STATE_DISABLED) {
		/* don't try to resolve children of a disabled optional */
		*finished = CIL_TREE_SKIP_HEAD;
		rc = SEPOL_OK;
		goto exit;
	}

	if (node->flavor == CIL_BLOCK && ((((struct cil_block*)node->data)->is_abstract == CIL_TRUE) && (pass > CIL_PASS_BLKABS))) {
		*finished = CIL_TREE_SKIP_HEAD;
		rc = SEPOL_OK;
		goto exit;
	}

	rc = __cil_resolve_ast_node(node, extra_args);
	if (rc == SEPOL_ENOENT && optstack != NULL) {
		struct cil_optional *opt = (struct cil_optional *)optstack->data;
		cil_log(CIL_WARN, "Disabling optional %s at %d of %s\n", opt->datum.name, node->parent->line, node->parent->path);
		/* disable an optional if something failed to resolve */
		opt->datum.state = CIL_STATE_DISABLING;
		rc = SEPOL_OK;
	} else if (rc != SEPOL_OK) {
		cil_log(CIL_ERR, "Failed to resolve %s statement at %d of %s\n", cil_node_to_string(node), node->line, node->path);
		goto exit;
	}

	return rc;

exit:
	return rc;
}

int __cil_disable_children_helper(struct cil_tree_node *node, uint32_t *finished, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_args_resolve *args = extra_args;
	uint32_t *changed = args->changed;

	if (node == NULL || finished == NULL) {
		goto exit;
	}

	if (node->flavor < CIL_MIN_DECLARATIVE) {
		/* only declarative statements need to be disabled */
		rc = SEPOL_OK;
		goto exit;
	}

	if (node->flavor == CIL_OPTIONAL) {
		if (((struct cil_symtab_datum *)node->data)->state == CIL_STATE_DISABLED) {
			/* don't bother going into an optional that isn't enabled */
			*finished = CIL_TREE_SKIP_HEAD;
			rc = SEPOL_OK;
			goto exit;
		}
	} else {
		/* Do we need to reset for a block? */
		*changed = 1;
	}

	((struct cil_symtab_datum *)node->data)->state = CIL_STATE_DISABLED;

	return SEPOL_OK;

exit:
	return rc;
}

int __cil_resolve_ast_first_child_helper(struct cil_tree_node *current, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_args_resolve *args = extra_args;
	struct cil_tree_node *callstack = NULL;
	struct cil_tree_node *optstack = NULL;
	struct cil_tree_node *parent = NULL;

	if (current == NULL || extra_args == NULL) {
		goto exit;
	}

	callstack = args->callstack;
	optstack = args->optstack;
	parent = current->parent;

	if (parent->flavor == CIL_CALL || parent->flavor == CIL_OPTIONAL) {
		/* push this node onto a stack */
		struct cil_tree_node *new;
		cil_tree_node_init(&new);

		new->data = parent->data;
		new->flavor = parent->flavor;

		if (parent->flavor == CIL_CALL) {
			if (callstack != NULL) {
				struct cil_tree_node *curr = NULL;
				struct cil_call *new_call = new->data;
				for (curr = callstack->cl_head; curr != NULL;
					curr = curr->cl_head) {
					struct cil_call *curr_call = curr->data;
					if (curr_call->macro == new_call->macro) {
						cil_log(CIL_ERR, "Recursive macro call found\n");
						rc = SEPOL_ERR;
						goto exit;
					}
				}
				callstack->parent = new;
				new->cl_head = callstack;
			}
			args->callstack = new;
		} else if (parent->flavor == CIL_OPTIONAL) {
			if (optstack != NULL) {
				optstack->parent = new;
				new->cl_head = optstack;
			}
			args->optstack = new;
		}
	} else if (parent->flavor == CIL_BOOLEANIF) {
		args->boolif = parent;
	} else if (parent->flavor == CIL_MACRO) {
		args->macro = parent;
	}

	return SEPOL_OK;

exit:
	return rc;

}

int __cil_resolve_ast_last_child_helper(struct cil_tree_node *current, void *extra_args)
{
	int rc = SEPOL_ERR;
	struct cil_args_resolve *args = extra_args;
	struct cil_tree_node *parent = NULL;

	if (current == NULL ||  extra_args == NULL) {
		goto exit;
	}

	parent = current->parent;

	if (parent->flavor == CIL_CALL) {
		/* pop off the stack */
		struct cil_tree_node *callstack = args->callstack;
		args->callstack = callstack->cl_head;
		if (callstack->cl_head) {
			callstack->cl_head->parent = NULL;
		}
		free(callstack);
	} else if (parent->flavor == CIL_MACRO) {
		args->macro = NULL;
	} else if (parent->flavor == CIL_OPTIONAL) {
		struct cil_tree_node *optstack;

		if (((struct cil_optional *)parent->data)->datum.state == CIL_STATE_DISABLING) {
			/* go into the optional, removing everything that it added */
			if (args->pass >= CIL_PASS_CALL1) {
				rc = cil_tree_walk(parent, __cil_disable_children_helper, NULL, NULL, extra_args);
				if (rc != SEPOL_OK) {
					cil_log(CIL_ERR, "Failed to disable declarations in optional\n");
					goto exit;
				}
			}
			((struct cil_optional *)parent->data)->datum.state = CIL_STATE_DISABLED;
		}

		/* pop off the stack */
		optstack = args->optstack;
		args->optstack = optstack->cl_head;
		if (optstack->cl_head) {
			optstack->cl_head->parent = NULL;
		}
		free(optstack);
	} else if (parent->flavor == CIL_BOOLEANIF) {
		args->boolif = NULL;
	}

	return SEPOL_OK;

exit:
	return rc;
}

int cil_resolve_ast(struct cil_db *db, struct cil_tree_node *current)
{
	int rc = SEPOL_ERR;
	struct cil_args_resolve extra_args;
	enum cil_pass pass = CIL_PASS_TIF;
	uint32_t changed = 0;

	if (db == NULL || current == NULL) {
		goto exit;
	}

	extra_args.db = db;
	extra_args.pass = pass;
	extra_args.changed = &changed;
	extra_args.callstack = NULL;
	extra_args.optstack = NULL;
	extra_args.boolif= NULL;
	extra_args.macro = NULL;
	extra_args.sidorder_lists = NULL;
	extra_args.classorder_lists = NULL;
	extra_args.catorder_lists = NULL;
	extra_args.sensitivityorder_lists = NULL;
	extra_args.in_list = NULL;

	cil_list_init(&extra_args.sidorder_lists, CIL_LIST_ITEM);
	cil_list_init(&extra_args.classorder_lists, CIL_LIST_ITEM);
	cil_list_init(&extra_args.catorder_lists, CIL_LIST_ITEM);
	cil_list_init(&extra_args.sensitivityorder_lists, CIL_LIST_ITEM);
	cil_list_init(&extra_args.in_list, CIL_IN);
	for (pass = CIL_PASS_TIF; pass < CIL_PASS_NUM; pass++) {
		extra_args.pass = pass;
		rc = cil_tree_walk(current, __cil_resolve_ast_node_helper, __cil_resolve_ast_first_child_helper, __cil_resolve_ast_last_child_helper, &extra_args);
		if (rc != SEPOL_OK) {
			cil_log(CIL_INFO, "Pass %i of resolution failed\n", pass);
			goto exit;
		}

		if (pass == CIL_PASS_IN) {
			rc = cil_resolve_in_list(&extra_args);
			if (rc != SEPOL_OK) {
				goto exit;
			}
			cil_list_destroy(&extra_args.in_list, CIL_FALSE);
		}

		if (pass == CIL_PASS_MISC1) {
			db->sidorder = __cil_ordered_lists_merge_all(&extra_args.sidorder_lists);
			db->classorder = __cil_ordered_lists_merge_all(&extra_args.classorder_lists);
			db->catorder = __cil_ordered_lists_merge_all(&extra_args.catorder_lists);
			cil_set_cat_values(db->catorder, db);
			db->sensitivityorder = __cil_ordered_lists_merge_all(&extra_args.sensitivityorder_lists);

			rc = __cil_verify_ordered(current, CIL_SID);
			if (rc != SEPOL_OK) {
				goto exit;
			}

			rc = __cil_verify_ordered(current, CIL_CLASS);
			if (rc != SEPOL_OK) {
				goto exit;
			}

			rc = __cil_verify_ordered(current, CIL_CAT);
			if (rc != SEPOL_OK) {
				goto exit;
			}

			rc = __cil_verify_ordered(current, CIL_SENS);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}

		if (changed && (pass > CIL_PASS_CALL1)) {
			/* Need to re-resolve because an optional was disabled that contained
			 * one or more declarations. We only need to reset to the call1 pass 
			 * because things done in the preceeding passes aren't allowed in 
			 * optionals, and thus can't be disabled.
			 * Note: set pass to CIL_PASS_CALL1 because the pass++ will increment 
			 * it to CIL_PASS_CALL2
			 */
			cil_log(CIL_INFO, "Resetting declarations\n");

			if (pass >= CIL_PASS_MISC1) {
				__cil_ordered_lists_reset(&extra_args.sidorder_lists);
				__cil_ordered_lists_reset(&extra_args.classorder_lists);
				__cil_ordered_lists_reset(&extra_args.catorder_lists);
				__cil_ordered_lists_reset(&extra_args.sensitivityorder_lists);
				cil_list_destroy(&db->sidorder, CIL_FALSE);
				cil_list_destroy(&db->classorder, CIL_FALSE);
				cil_list_destroy(&db->catorder, CIL_FALSE);
				cil_list_destroy(&db->sensitivityorder, CIL_FALSE);
			}

			pass = CIL_PASS_CALL1;

			rc = cil_reset_ast(current);
			if (rc != SEPOL_OK) {
				cil_log(CIL_ERR, "Failed to reset declarations\n");
				goto exit;
			}
		}

		/* reset the arguments */
		changed = 0;
		while (extra_args.callstack != NULL) {
			struct cil_tree_node *curr = extra_args.callstack;
			struct cil_tree_node *next = curr->cl_head;
			free(curr);
			extra_args.callstack = next;
		}
		while (extra_args.optstack != NULL) {
			struct cil_tree_node *curr = extra_args.optstack;
			struct cil_tree_node *next = curr->cl_head;
			free(curr);
			extra_args.optstack = next;
		}
	}

	rc = __cil_verify_initsids(db->sidorder);
	if (rc != SEPOL_OK) {
		goto exit;
	}

	rc = SEPOL_OK;
exit:
	return rc;
}

static int __cil_resolve_name_helper(struct cil_tree_node *ast_node, char *name, enum cil_sym_index sym_index, void *extra_args, struct cil_symtab_datum **datum)
{
	struct cil_args_resolve *args = extra_args;
	struct cil_call *call = NULL;
	struct cil_tree_node *macro = NULL;
	enum cil_pass pass = CIL_PASS_INIT;

	int rc = SEPOL_ERR;
	char* name_dup = cil_strdup(name);
	char *tok_current = strtok(name_dup, ".");
	char *tok_next = strtok(NULL, ".");
	symtab_t *symtab = NULL;
	struct cil_symtab_datum *tmp_datum = NULL;
	enum cil_flavor flavor = CIL_NONE;

	if (args != NULL) {
		if (args->callstack != NULL) {
			call = args->callstack->data;
		}
		pass = args->pass;
		macro = args->macro;
	}

	if (ast_node->flavor == CIL_ROOT) {
		symtab = &((struct cil_root *)ast_node->data)->symtab[CIL_SYM_BLOCKS];
	} else {
		if (call != NULL) {
			// check macro symtab
			symtab = &call->macro->symtab[CIL_SYM_BLOCKS];
			rc = cil_symtab_get_datum(symtab, tok_current, datum);
			if (rc == SEPOL_OK) {
				flavor = ((struct cil_tree_node*)(*datum)->nodes->head->data)->flavor;
				if (flavor != CIL_BLOCK) {
					printf("Failed to get block from symtab\n");
					rc = SEPOL_ERR;
					goto exit;
				}
				// if in macro, check call parent to verify successful copy to call
				rc = cil_get_symtab(ast_node->parent->parent, &symtab, CIL_SYM_BLOCKS);
				if (rc == SEPOL_OK) {
					rc = cil_symtab_get_datum(symtab, tok_current, datum);
					flavor = ((struct cil_tree_node*)(*datum)->nodes->head->data)->flavor;
					if (rc != SEPOL_OK) {
						cil_log(CIL_ERR, "Failed to get datum from parent symtab of call\n");
						goto exit;
					} else if (flavor != CIL_BLOCK) {
						printf("Failed to get block from symtab\n");
						rc = SEPOL_ERR;
						goto exit;
					}
				} else {
					cil_log(CIL_ERR, "Failed to get symtab from call parent\n");
					goto exit;
				}
			} else if (rc == SEPOL_ENOENT) {
				rc = cil_get_symtab(((struct cil_tree_node*)call->macro->datum.nodes->head->data)->parent, &symtab, CIL_SYM_BLOCKS);
				if (rc != SEPOL_OK) {
					cil_log(CIL_ERR, "Failed to get datum from parent symtab of macro\n");
					goto exit;
				}
			} else {
				goto exit;
			}

		} else {
			if (ast_node->flavor == CIL_TUNABLEIF && macro != NULL) {
				rc = cil_get_symtab(macro->parent, &symtab, CIL_SYM_BLOCKS);
			} else {
				rc = cil_get_symtab(ast_node->parent, &symtab, CIL_SYM_BLOCKS);
			}
			if (rc != SEPOL_OK) {
				cil_log(CIL_ERR, "Failed to get parent symtab, rc: %d\n", rc);
				goto exit;
			}
		}
	}

	if (tok_next == NULL) {
		/*TODO: Should this set rc to SEPOL_ERR? */
		/* Cant this be done earlier */
		goto exit;
	}

	while (tok_current != NULL) {
		if (tok_next != NULL) {
			rc = cil_symtab_get_datum(symtab, tok_current, &tmp_datum);
			if (rc == SEPOL_OK) {
				flavor = ((struct cil_tree_node*)tmp_datum->nodes->head->data)->flavor;
			} else {
				goto exit;
			}
 
			if ((flavor != CIL_BLOCK && ast_node->flavor != CIL_IN) ||
					(flavor == CIL_BLOCK && (((struct cil_block*)tmp_datum)->is_abstract == CIL_TRUE && pass > CIL_PASS_BLKABS ))) {
				printf("Failed to resolve block: %s\n", tok_current);
				rc = SEPOL_ERR;
				goto exit;
			}
			symtab = &(((struct cil_block*)tmp_datum)->symtab[CIL_SYM_BLOCKS]);
		} else {
			//cil_log(CIL_ERR, "type key: %s\n", tok_current);
			symtab = &(((struct cil_block*)tmp_datum)->symtab[sym_index]);
			rc = cil_symtab_get_datum(symtab, tok_current, &tmp_datum);
			if (rc != SEPOL_OK) {
				goto exit;
			}
		}
		tok_current = tok_next;
		tok_next = strtok(NULL, ".");
	}
	*datum = tmp_datum;
	free(name_dup);

	return SEPOL_OK;

exit:
	free(name_dup);
	return rc;
}

int cil_resolve_name(struct cil_tree_node *ast_node, char *name, enum cil_sym_index sym_index, void *extra_args, struct cil_symtab_datum **datum)
{
	struct cil_args_resolve *args = extra_args;
	struct cil_db *db = NULL;
	struct cil_call *call = NULL;
	struct cil_tree_node *node = NULL;
	struct cil_tree_node *macro = NULL;
	struct cil_tree_node *namespace = NULL;
	int rc = SEPOL_ERR;
	char *global_symtab_name = NULL;
	char first;

	if (args != NULL) {
		db = args->db;
		if (args->callstack != NULL) {
			call = args->callstack->data;
		}
		macro = args->macro;
	}

	if (db == NULL || ast_node == NULL || name == NULL) {
		cil_log(CIL_ERR, "Invalid call to cil_resolve_name\n");
		goto exit;
	}

	global_symtab_name = name;
	first = *name;

	if (first != '.') {
		if (strrchr(name, '.') == NULL) {
			symtab_t *symtab = NULL;
			if (call != NULL) {
				namespace = ast_node;
				while (namespace->flavor != CIL_BLOCK && namespace->flavor != CIL_CALL) {
					namespace = namespace->parent;
				}
				if (namespace->flavor == CIL_BLOCK) {
					rc = cil_get_symtab(namespace, &symtab, sym_index);
					if (rc != SEPOL_OK) {
						cil_log(CIL_ERR, "Failed to get parent symtab\n");
						goto exit;
					}
				} else {
					symtab = &call->macro->symtab[sym_index];
					rc = cil_symtab_get_datum(symtab, name, datum);
					if (rc == SEPOL_OK) {
						rc = cil_get_symtab(namespace, &symtab, sym_index);
						if (rc != SEPOL_OK) {
							cil_log(CIL_ERR, "Failed to get parent symtab from call\n");
							goto exit;
						}
					}
				}

				rc = cil_symtab_get_datum(symtab, name, datum);
				if (rc != SEPOL_OK) {
					rc = cil_resolve_name_call_args(call, name, sym_index, datum);
					if (rc == SEPOL_OK) {
						goto exit;
					}

					rc = cil_get_symtab(((struct cil_tree_node*)call->macro->datum.nodes->head->data)->parent, &symtab, sym_index);
					if (rc != SEPOL_OK) {
						goto exit;
					}

					rc = cil_symtab_get_datum(symtab, name, datum);
					if (rc == SEPOL_OK) {
						goto exit;
					}

					global_symtab_name = cil_malloc(strlen(name)+2);
					strcpy(global_symtab_name, ".");
					strncat(global_symtab_name, name, strlen(name));
				}
			} else {
				if (ast_node->flavor == CIL_TUNABLEIF && macro != NULL) {
					rc = cil_get_symtab(macro->parent, &symtab, sym_index);
				} else {
					rc = cil_get_symtab(ast_node->parent, &symtab, sym_index);
				}
				if (rc != SEPOL_OK) {
					cil_log(CIL_ERR, "Failed to get parent symtab, rc: %d\n", rc);
					goto exit;
				}
				rc = cil_symtab_get_datum(symtab, name, datum);
				if (rc != SEPOL_OK) {
					global_symtab_name = cil_malloc(strlen(name)+2);
					strcpy(global_symtab_name, ".");
					strncat(global_symtab_name, name, strlen(name));
				}
			}
		} else {
			rc = __cil_resolve_name_helper(ast_node, name, sym_index, args, datum);
			if (rc != SEPOL_OK) {
				global_symtab_name = cil_malloc(strlen(name)+2);
				strcpy(global_symtab_name, ".");
				strncat(global_symtab_name, name, strlen(name));
			}
		}
	}

	first = *global_symtab_name;

	if (first == '.') {
		if (strrchr(global_symtab_name, '.') == global_symtab_name) { //Only one dot in name, check global symtabs
			symtab_t *symtab = &((struct cil_root *)db->ast->root->data)->symtab[sym_index];
			rc = cil_symtab_get_datum(symtab, global_symtab_name+1, datum);
			if (rc != SEPOL_OK) {
				free(global_symtab_name);
				goto exit;
			}
		} else {
			rc = __cil_resolve_name_helper(db->ast->root, global_symtab_name, sym_index, args, datum);
			if (rc != SEPOL_OK) {
				free(global_symtab_name);
				goto exit;
			}
		}
	}

	if (global_symtab_name != name) {
		free(global_symtab_name);
	}
	
	rc = SEPOL_OK;

exit:
	if (rc != SEPOL_OK) {
		cil_log(CIL_WARN, "Failed to resolve %s in %s statement on line %d of %s\n", 
			name, cil_node_to_string(ast_node), ast_node->line, ast_node->path);
	}

	if (*datum != NULL) {
		/* If this datum is an alias, then return the actual node
		 * This depends on aliases already being processed
		 */
		node = (*datum)->nodes->head->data;
		if (node->flavor == CIL_TYPEALIAS || node->flavor == CIL_SENSALIAS
			|| node->flavor == CIL_CATALIAS) {
			struct cil_alias *alias = (struct cil_alias *)(*datum);
			if (alias->actual) {
				*datum = alias->actual;
			}
		}
	}

	return rc;
}
