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
static SCM scm_parse_face_bool_attribute = SCM_BOOL_F;
static SCM scm_process_yesno_response = SCM_BOOL_F;
static SCM scm_filter_dbus_message = SCM_BOOL_F;
static SCM scm_is_special_buffer_name = SCM_BOOL_F;

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

  scm_parse_face_bool_attribute = scm_c_module_lookup (elisp_emacs_module, "parse-face-bool-attribute");
  if (scm_is_false (scm_parse_face_bool_attribute))
    scm_parse_face_bool_attribute = scm_c_lookup ("parse-face-bool-attribute");

  scm_process_yesno_response = scm_c_module_lookup (elisp_emacs_module, "process-yesno-response");
  if (scm_is_false (scm_process_yesno_response))
    scm_process_yesno_response = scm_c_lookup ("process-yesno-response");

  scm_filter_dbus_message = scm_c_module_lookup (elisp_emacs_module, "filter-dbus-message");
  if (scm_is_false (scm_filter_dbus_message))
    scm_filter_dbus_message = scm_c_lookup ("filter-dbus-message");

  scm_is_special_buffer_name = scm_c_module_lookup (elisp_emacs_module, "is-special-buffer-name?");
  if (scm_is_false (scm_is_special_buffer_name))
    scm_is_special_buffer_name = scm_c_lookup ("is-special-buffer-name?");

  /* Protect from GC */
  scm_gc_protect_object (scm_lookup_color_in_map);
  scm_gc_protect_object (scm_lookup_font_style);
  scm_gc_protect_object (scm_lookup_in_alist_ci);
  scm_gc_protect_object (scm_lookup_in_alist);
  scm_gc_protect_object (scm_lookup_symbol_in_list);
  scm_gc_protect_object (scm_parse_face_bool_attribute);
  scm_gc_protect_object (scm_process_yesno_response);
  scm_gc_protect_object (scm_filter_dbus_message);
  scm_gc_protect_object (scm_is_special_buffer_name);
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

/* Parse face boolean attribute */
int
guile_parse_face_bool_attribute (Lisp_Object attr_string)
{
  if (!scm_is_true (scm_parse_face_bool_attribute))
    return 0; /* unknown */

  if (!STRINGP (attr_string))
    return 0; /* unknown */

  SCM result = scm_call_1 (scm_parse_face_bool_attribute,
                           scm_from_utf8_string (SSDATA (attr_string)));

  if (scm_is_eq (result, scm_from_utf8_symbol ("true")))
    return 1;
  else if (scm_is_eq (result, scm_from_utf8_symbol ("false")))
    return -1;
  else
    return 0; /* nil/unknown */
}

/* Process yes/no response */
int
guile_process_yesno_response (Lisp_Object response_string)
{
  if (!scm_is_true (scm_process_yesno_response))
    return -1; /* invalid */

  if (!STRINGP (response_string))
    return -1; /* invalid */

  SCM result = scm_call_1 (scm_process_yesno_response,
                           scm_from_utf8_string (SSDATA (response_string)));

  if (scm_is_eq (result, scm_from_utf8_symbol ("yes")))
    return 1;
  else if (scm_is_eq (result, scm_from_utf8_symbol ("no")))
    return 0;
  else
    return -1; /* invalid */
}

/* Filter DBus message */
bool
guile_filter_dbus_message (Lisp_Object message, Lisp_Object interface_pattern, Lisp_Object member_pattern)
{
  if (!scm_is_true (scm_filter_dbus_message))
    return false;

  if (!STRINGP (interface_pattern) || !STRINGP (member_pattern))
    return false;

  SCM result = scm_call_3 (scm_filter_dbus_message,
                           message,
                           scm_from_utf8_string (SSDATA (interface_pattern)),
                           scm_from_utf8_string (SSDATA (member_pattern)));

  return scm_is_true (result);
}

/* Check if buffer name is special */
bool
guile_is_special_buffer_name (Lisp_Object buffer_name)
{
  if (!scm_is_true (scm_is_special_buffer_name))
    return false;

  if (!STRINGP (buffer_name))
    return false;

  SCM result = scm_call_1 (scm_is_special_buffer_name,
                           scm_from_utf8_string (SSDATA (buffer_name)));

  return scm_is_true (result);
}
