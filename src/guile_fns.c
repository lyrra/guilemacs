/* guile_lookups.c - Bridge to Guile lookup functions */

#include <config.h>
#include "lisp.h"
#include "guile_fns.h"
#include <libguile.h>

/* Scheme function references */
static SCM scm_lookup_color_in_map = SCM_BOOL_F;
static SCM scm_lookup_font_style = SCM_BOOL_F;
static SCM scm_lookup_in_alist_ci = SCM_BOOL_F;
static SCM scm_lookup_in_alist = SCM_BOOL_F;
static SCM scm_lookup_symbol_in_list = SCM_BOOL_F;

/* Initialize the Guile lookup functions module */
void
init_guile_fns (void)
{
  /* Get references to the Scheme functions loaded by prelude/load.scm */
  /* Try to look them up from language elisp emacs module first, fallback to global */

  SCM elisp_emacs_module = scm_c_resolve_module ("language elisp emacs");

  scm_lookup_color_in_map = scm_c_module_lookup (elisp_emacs_module, "lookup-color-in-map");
  if (scm_is_false (scm_lookup_color_in_map))
    scm_lookup_color_in_map = scm_c_lookup ("lookup-color-in-map");

  scm_lookup_font_style = scm_c_module_lookup (elisp_emacs_module, "lookup-font-style");
  if (scm_is_false (scm_lookup_font_style))
    scm_lookup_font_style = scm_c_lookup ("lookup-font-style");

  scm_lookup_in_alist_ci = scm_c_module_lookup (elisp_emacs_module, "lookup-in-alist-ci");
  if (scm_is_false (scm_lookup_in_alist_ci))
    scm_lookup_in_alist_ci = scm_c_lookup ("lookup-in-alist-ci");

  scm_lookup_in_alist = scm_c_module_lookup (elisp_emacs_module, "lookup-in-alist");
  if (scm_is_false (scm_lookup_in_alist))
    scm_lookup_in_alist = scm_c_lookup ("lookup-in-alist");

  scm_lookup_symbol_in_list = scm_c_module_lookup (elisp_emacs_module, "lookup-symbol-in-list");
  if (scm_is_false (scm_lookup_symbol_in_list))
    scm_lookup_symbol_in_list = scm_c_lookup ("lookup-symbol-in-list");

  /* Protect from GC */
  scm_gc_protect_object (scm_lookup_color_in_map);
  scm_gc_protect_object (scm_lookup_font_style);
  scm_gc_protect_object (scm_lookup_in_alist_ci);
  scm_gc_protect_object (scm_lookup_in_alist);
  scm_gc_protect_object (scm_lookup_symbol_in_list);
}

/* Lookup a color by name in a color map */
Lisp_Object
guile_lookup_color (Lisp_Object color_map, const char *color_name)
{
  if (!scm_is_true (scm_lookup_color_in_map))
    return Qnil;

  SCM result = scm_call_2 (scm_lookup_color_in_map,
                           color_map,
                           scm_from_utf8_string (color_name));

  if (scm_is_false (result))
    return Qnil;

  return result;
}

/* Lookup a font style in a font style table */
Lisp_Object
guile_lookup_font_style (Lisp_Object table, const char *style_name)
{
  if (!scm_is_true (scm_lookup_font_style))
    return Qnil;

  SCM result = scm_call_2 (scm_lookup_font_style,
                           table,
                           scm_from_utf8_string (style_name));

  if (scm_is_false (result))
    return Qnil;

  /* Result is (cons table-index element-index) */
  if (scm_is_pair (result))
    {
      SCM car = scm_car (result);
      SCM cdr = scm_cdr (result);

      if (scm_is_integer (car) && scm_is_integer (cdr))
        {
          int i = scm_to_int (car);
          int j = scm_to_int (cdr);
          return Fcons (make_fixnum (i), make_fixnum (j));
        }
    }

  return Qnil;
}

/* Lookup in an alist with case-insensitive comparison */
Lisp_Object
guile_lookup_alist_ci (Lisp_Object alist, const char *key)
{
  if (!scm_is_true (scm_lookup_in_alist_ci))
    return Qnil;

  SCM result = scm_call_2 (scm_lookup_in_alist_ci,
                           alist,
                           scm_from_utf8_string (key));

  if (scm_is_false (result))
    return Qnil;

  return result;
}

/* Lookup in an alist with case-sensitive comparison */
Lisp_Object
guile_lookup_alist (Lisp_Object alist, const char *key)
{
  if (!scm_is_true (scm_lookup_in_alist))
    return Qnil;

  SCM result = scm_call_2 (scm_lookup_in_alist,
                           alist,
                           scm_from_utf8_string (key));

  if (scm_is_false (result))
    return Qnil;

  return result;
}

/* Check if a symbol name exists in a list */
bool
guile_lookup_symbol_in_list (Lisp_Object list, const char *name)
{
  if (!scm_is_true (scm_lookup_symbol_in_list))
    return false;

  SCM result = scm_call_2 (scm_lookup_symbol_in_list,
                           list,
                           scm_from_utf8_string (name));

  return scm_is_true (result);
}
