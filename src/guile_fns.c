/* guile_lookups.c - Bridge to Guile lookup functions */

#include <config.h>
#include "lisp.h"
#include "guile.h"
#include "guile_fns.h"
#include "coding.h"
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
static SCM scm_parse_color_spec = SCM_BOOL_F;
static SCM scm_validate_color_name = SCM_BOOL_F;
static SCM scm_string_contains_whitespace = SCM_BOOL_F;
static SCM scm_is_frame_name_fnn_format = SCM_BOOL_F;
static SCM scm_validate_xlfd_font_name = SCM_BOOL_F;
static SCM scm_string_spaces_to_dashes = SCM_BOOL_F;
static SCM scm_string_trim_leading_whitespace = SCM_BOOL_F;
static SCM scm_parse_number_string = SCM_BOOL_F;
static SCM scm_validate_string_for_copying = SCM_BOOL_F;
static SCM scm_prepare_string_for_symbol = SCM_BOOL_F;

/* New scheme function references for additional SSDATA hoisting */
static SCM scm_has_file_extension = SCM_BOOL_F;
static SCM scm_extract_filename_from_path = SCM_BOOL_F;
static SCM scm_is_modifier_symbol = SCM_BOOL_F;
static SCM scm_validate_float_format_string = SCM_BOOL_F;
static SCM scm_has_time_format_specifiers = SCM_BOOL_F;
static SCM scm_parse_hex_color = SCM_BOOL_F;
static SCM scm_needs_filename_conversion = SCM_BOOL_F;
static SCM scm_is_utf8_filename = SCM_BOOL_F;
static SCM scm_is_safe_for_c_string_copy = SCM_BOOL_F;
static SCM scm_looks_like_network_address = SCM_BOOL_F;

/* Path/Filename operation function references */
static SCM scm_is_absolute_path = SCM_BOOL_F;
static SCM scm_ends_with_directory_separator = SCM_BOOL_F;
static SCM scm_normalize_path_separators = SCM_BOOL_F;
static SCM scm_string_empty = SCM_BOOL_F;
static SCM scm_has_directory_traversal = SCM_BOOL_F;
static SCM scm_get_file_extension = SCM_BOOL_F;
static SCM scm_path_starts_with = SCM_BOOL_F;

/* Simple string validation function references */
static SCM scm_string_single_char = SCM_BOOL_F;
static SCM scm_string_starts_with_space = SCM_BOOL_F;
static SCM scm_string_ascii_only = SCM_BOOL_F;
static SCM scm_valid_symbol_name = SCM_BOOL_F;
static SCM scm_string_numeric = SCM_BOOL_F;
static SCM scm_string_needs_escaping = SCM_BOOL_F;
static SCM scm_special_buffer_name = SCM_BOOL_F;
static SCM scm_string_equal_ignore_case = SCM_BOOL_F;
static SCM scm_string_starts_with_char = SCM_BOOL_F;
static SCM scm_string_ends_with_char = SCM_BOOL_F;
static SCM scm_string_whitespace_only = SCM_BOOL_F;
static SCM scm_valid_identifier = SCM_BOOL_F;

/* File extension and type checking function references */
static SCM scm_source_code_file = SCM_BOOL_F;
static SCM scm_image_file = SCM_BOOL_F;
static SCM scm_config_file = SCM_BOOL_F;
static SCM scm_extract_file_extension = SCM_BOOL_F;

/* Font and color validation function references */
static SCM scm_hex_color_string = SCM_BOOL_F;
static SCM scm_rgb_color_string = SCM_BOOL_F;
static SCM scm_named_color = SCM_BOOL_F;
static SCM scm_valid_xlfd_font_name = SCM_BOOL_F;
static SCM scm_font_family_name = SCM_BOOL_F;

/* Network and URL validation function references */
static SCM scm_url_string = SCM_BOOL_F;
static SCM scm_email_address = SCM_BOOL_F;
static SCM scm_ip_address = SCM_BOOL_F;

/* Registry to script mapping function reference */
static SCM scm_lookup_registry_to_script = SCM_BOOL_F;

/* Font name parsing function reference */
static SCM scm_parse_font_name_with_size = SCM_BOOL_F;

/* String operations without properties function reference */
static SCM scm_substring_no_properties_scheme = SCM_BOOL_F;

/* File path operation function references */
static SCM scm_file_path_absolute_p = SCM_BOOL_F;
static SCM scm_file_path_directory = SCM_BOOL_F;
static SCM scm_file_path_nondirectory = SCM_BOOL_F;
static SCM scm_file_path_safe_p = SCM_BOOL_F;

/* String concatenation function references */
static SCM scm_string_concat_2 = SCM_BOOL_F;
static SCM scm_string_concat_3 = SCM_BOOL_F;
static SCM scm_string_concat_multi = SCM_BOOL_F;

/* Integer parsing function references */
static SCM scm_parse_integer_string = SCM_BOOL_F;
static SCM scm_read_integer_guile = SCM_BOOL_F;
static SCM scm_parse_emacs_number = SCM_BOOL_F;

/* Helper function to safely lookup a procedure from a module.
   Returns SCM_BOOL_F if not found or unbound, the procedure otherwise. */
static SCM
safe_public_ref (const char *module, const char *name)
{
  SCM mod = scm_c_resolve_module (module);
  SCM var = scm_module_variable (mod, scm_from_utf8_symbol (name));
  if (scm_is_false (var))
    return SCM_BOOL_F;
  /* Check if the variable is bound before trying to get its value */
  if (scm_is_false (scm_variable_bound_p (var)))
    return SCM_BOOL_F;
  SCM val = scm_variable_ref (var);
  /* Return the value only if it's a procedure */
  if (scm_is_true (scm_procedure_p (val)))
    return val;
  return SCM_BOOL_F;
}

/* Initialize the Guile lookup functions module */
void
init_guile_fns (void)
{
  /* Get direct references to the Scheme functions (not variables).
     This avoids issues with scm_variable_ref on unbound variables.
     We use safe_public_ref which returns #f for missing bindings. */

  scm_lookup_color_in_map = safe_public_ref ("language elisp emacs", "lookup-color-in-map");
  scm_lookup_font_style = safe_public_ref ("language elisp emacs", "lookup-font-style");
  scm_lookup_in_alist_ci = safe_public_ref ("language elisp emacs", "lookup-in-alist-ci");
  scm_lookup_in_alist = safe_public_ref ("language elisp emacs", "lookup-in-alist");
  scm_lookup_symbol_in_list = safe_public_ref ("language elisp emacs", "lookup-symbol-in-list");
  scm_parse_face_bool_attribute = safe_public_ref ("language elisp emacs", "parse-face-bool-attribute");
  scm_process_yesno_response = safe_public_ref ("language elisp emacs", "process-yesno-response");
  scm_filter_dbus_message = safe_public_ref ("language elisp emacs", "filter-dbus-message");
  scm_is_special_buffer_name = safe_public_ref ("language elisp emacs", "is-special-buffer-name?");
  scm_parse_color_spec = safe_public_ref ("language elisp emacs", "parse-color-spec");
  scm_validate_color_name = safe_public_ref ("language elisp emacs", "validate-color-name");
  scm_string_contains_whitespace = safe_public_ref ("language elisp emacs", "string-contains-whitespace?");
  scm_is_frame_name_fnn_format = safe_public_ref ("language elisp emacs", "is-frame-name-fnn-format?");
  scm_validate_xlfd_font_name = safe_public_ref ("language elisp emacs", "validate-xlfd-font-name");
  scm_is_absolute_path = safe_public_ref ("language elisp emacs", "is-absolute-path?");
  scm_has_directory_traversal = safe_public_ref ("language elisp emacs", "has-directory-traversal?");
  scm_string_spaces_to_dashes = safe_public_ref ("language elisp emacs", "string-spaces-to-dashes");
  scm_string_trim_leading_whitespace = safe_public_ref ("language elisp emacs", "string-trim-leading-whitespace");
  scm_parse_number_string = safe_public_ref ("language elisp emacs", "parse-number-string");
  scm_validate_string_for_copying = safe_public_ref ("language elisp emacs", "validate-string-for-copying");
  scm_prepare_string_for_symbol = safe_public_ref ("language elisp emacs", "prepare-string-for-symbol");

  /* New scheme functions */
  scm_has_file_extension = safe_public_ref ("language elisp emacs", "has-file-extension?");
  scm_extract_filename_from_path = safe_public_ref ("language elisp emacs", "extract-filename-from-path");
  scm_is_modifier_symbol = safe_public_ref ("language elisp emacs", "is-modifier-symbol?");
  scm_validate_float_format_string = safe_public_ref ("language elisp emacs", "validate-float-format-string");
  scm_has_time_format_specifiers = safe_public_ref ("language elisp emacs", "has-time-format-specifiers?");
  scm_parse_hex_color = safe_public_ref ("language elisp emacs", "parse-hex-color");
  scm_needs_filename_conversion = safe_public_ref ("language elisp emacs", "needs-filename-conversion?");
  scm_is_utf8_filename = safe_public_ref ("language elisp emacs", "is-utf8-filename?");
  scm_is_safe_for_c_string_copy = safe_public_ref ("language elisp emacs", "is-safe-for-c-string-copy?");
  scm_looks_like_network_address = safe_public_ref ("language elisp emacs", "looks-like-network-address?");

  /* Path/filename operation functions */
  scm_ends_with_directory_separator = safe_public_ref ("language elisp emacs", "ends-with-directory-separator?");
  scm_normalize_path_separators = safe_public_ref ("language elisp emacs", "normalize-path-separators");
  scm_string_empty = safe_public_ref ("language elisp emacs", "string-empty?");
  scm_get_file_extension = safe_public_ref ("language elisp emacs", "get-file-extension");
  scm_path_starts_with = safe_public_ref ("language elisp emacs", "path-starts-with?");

  /* Simple string validation functions */
  scm_string_single_char = safe_public_ref ("language elisp emacs", "string-single-char?");
  scm_string_starts_with_space = safe_public_ref ("language elisp emacs", "string-starts-with-space?");
  scm_string_ascii_only = safe_public_ref ("language elisp emacs", "string-ascii-only?");
  scm_valid_symbol_name = safe_public_ref ("language elisp emacs", "valid-symbol-name?");
  scm_string_numeric = safe_public_ref ("language elisp emacs", "string-numeric?");
  scm_string_needs_escaping = safe_public_ref ("language elisp emacs", "string-needs-escaping?");
  scm_special_buffer_name = safe_public_ref ("language elisp emacs", "special-buffer-name?");
  scm_string_equal_ignore_case = safe_public_ref ("language elisp emacs", "string-equal-ignore-case?");
  scm_string_starts_with_char = safe_public_ref ("language elisp emacs", "string-starts-with-char?");
  scm_string_ends_with_char = safe_public_ref ("language elisp emacs", "string-ends-with-char?");
  scm_string_whitespace_only = safe_public_ref ("language elisp emacs", "string-whitespace-only?");
  scm_valid_identifier = safe_public_ref ("language elisp emacs", "valid-identifier?");

  /* File extension and type checking functions */
  scm_source_code_file = safe_public_ref ("language elisp emacs", "source-code-file?");
  scm_image_file = safe_public_ref ("language elisp emacs", "image-file?");
  scm_config_file = safe_public_ref ("language elisp emacs", "config-file?");
  scm_extract_file_extension = safe_public_ref ("language elisp emacs", "extract-file-extension");

  /* Font and color validation functions */
  scm_hex_color_string = safe_public_ref ("language elisp emacs", "hex-color-string?");
  scm_rgb_color_string = safe_public_ref ("language elisp emacs", "rgb-color-string?");
  scm_named_color = safe_public_ref ("language elisp emacs", "named-color?");
  scm_valid_xlfd_font_name = safe_public_ref ("language elisp emacs", "valid-xlfd-font-name?");
  scm_font_family_name = safe_public_ref ("language elisp emacs", "font-family-name?");

  /* Network and URL validation functions */
  scm_url_string = safe_public_ref ("language elisp emacs", "url-string?");
  scm_email_address = safe_public_ref ("language elisp emacs", "email-address?");
  scm_ip_address = safe_public_ref ("language elisp emacs", "ip-address?");

  /* Registry to script mapping function */
  scm_lookup_registry_to_script = safe_public_ref ("language elisp emacs", "lookup-registry-to-script");

  /* Font name parsing function */
  scm_parse_font_name_with_size = safe_public_ref ("language elisp emacs", "parse-font-name-with-size");

  /* String operations function */
  scm_substring_no_properties_scheme = safe_public_ref ("language elisp emacs", "substring-no-properties-scheme");

  /* File path operation functions */
  scm_file_path_absolute_p = safe_public_ref ("language elisp emacs", "file-path-absolute-p");
  scm_file_path_directory = safe_public_ref ("language elisp emacs", "file-path-directory");
  scm_file_path_nondirectory = safe_public_ref ("language elisp emacs", "file-path-nondirectory");
  scm_file_path_safe_p = safe_public_ref ("language elisp emacs", "file-path-safe-p");

  /* String concatenation functions */
  scm_string_concat_2 = safe_public_ref ("language elisp emacs", "string-concat-2");
  scm_string_concat_3 = safe_public_ref ("language elisp emacs", "string-concat-3");
  scm_string_concat_multi = safe_public_ref ("language elisp emacs", "string-concat-multi");

  /* Integer parsing functions */
  scm_parse_integer_string = safe_public_ref ("language elisp emacs", "parse-integer-string");
  scm_read_integer_guile = safe_public_ref ("language elisp emacs", "read-integer-guile");
  scm_parse_emacs_number = safe_public_ref ("language elisp emacs", "parse-emacs-number");

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
  scm_gc_protect_object (scm_parse_color_spec);
  scm_gc_protect_object (scm_validate_color_name);
  scm_gc_protect_object (scm_string_contains_whitespace);
  scm_gc_protect_object (scm_is_frame_name_fnn_format);
  scm_gc_protect_object (scm_validate_xlfd_font_name);
  scm_gc_protect_object (scm_is_absolute_path);
  scm_gc_protect_object (scm_has_directory_traversal);
  scm_gc_protect_object (scm_string_spaces_to_dashes);
  scm_gc_protect_object (scm_string_trim_leading_whitespace);
  scm_gc_protect_object (scm_parse_number_string);
  scm_gc_protect_object (scm_validate_string_for_copying);
  scm_gc_protect_object (scm_prepare_string_for_symbol);

  /* Protect new scheme functions from GC */
  scm_gc_protect_object (scm_has_file_extension);
  scm_gc_protect_object (scm_extract_filename_from_path);
  scm_gc_protect_object (scm_is_modifier_symbol);
  scm_gc_protect_object (scm_validate_float_format_string);
  scm_gc_protect_object (scm_has_time_format_specifiers);
  scm_gc_protect_object (scm_parse_hex_color);
  scm_gc_protect_object (scm_needs_filename_conversion);
  scm_gc_protect_object (scm_is_utf8_filename);
  scm_gc_protect_object (scm_is_safe_for_c_string_copy);
  scm_gc_protect_object (scm_looks_like_network_address);

  /* Protect path/filename operation functions from GC */
  scm_gc_protect_object (scm_is_absolute_path);
  scm_gc_protect_object (scm_ends_with_directory_separator);
  scm_gc_protect_object (scm_normalize_path_separators);
  scm_gc_protect_object (scm_string_empty);
  scm_gc_protect_object (scm_has_directory_traversal);
  scm_gc_protect_object (scm_get_file_extension);
  scm_gc_protect_object (scm_path_starts_with);

  /* Protect simple string validation functions from GC */
  scm_gc_protect_object (scm_string_single_char);
  scm_gc_protect_object (scm_string_starts_with_space);
  scm_gc_protect_object (scm_string_ascii_only);
  scm_gc_protect_object (scm_valid_symbol_name);
  scm_gc_protect_object (scm_string_numeric);
  scm_gc_protect_object (scm_string_needs_escaping);
  scm_gc_protect_object (scm_special_buffer_name);
  scm_gc_protect_object (scm_string_equal_ignore_case);
  scm_gc_protect_object (scm_string_starts_with_char);
  scm_gc_protect_object (scm_string_ends_with_char);
  scm_gc_protect_object (scm_string_whitespace_only);
  scm_gc_protect_object (scm_valid_identifier);

  /* Protect file extension and type checking functions from GC */
  scm_gc_protect_object (scm_has_file_extension);
  scm_gc_protect_object (scm_source_code_file);
  scm_gc_protect_object (scm_image_file);
  scm_gc_protect_object (scm_config_file);
  scm_gc_protect_object (scm_extract_file_extension);

  /* Protect font and color validation functions from GC */
  scm_gc_protect_object (scm_hex_color_string);
  scm_gc_protect_object (scm_rgb_color_string);
  scm_gc_protect_object (scm_named_color);
  scm_gc_protect_object (scm_valid_xlfd_font_name);
  scm_gc_protect_object (scm_font_family_name);

  /* Protect network and URL validation functions from GC */
  scm_gc_protect_object (scm_url_string);
  scm_gc_protect_object (scm_email_address);
  scm_gc_protect_object (scm_ip_address);

  /* Protect registry to script mapping function from GC */
  scm_gc_protect_object (scm_lookup_registry_to_script);

  /* Protect font name parsing function from GC */
  scm_gc_protect_object (scm_parse_font_name_with_size);

  /* Protect string operations function from GC */
  scm_gc_protect_object (scm_substring_no_properties_scheme);

  /* Protect file path operation functions from GC */
  scm_gc_protect_object (scm_file_path_absolute_p);
  scm_gc_protect_object (scm_file_path_directory);
  scm_gc_protect_object (scm_file_path_nondirectory);
  scm_gc_protect_object (scm_file_path_safe_p);

  /* Protect string concatenation functions from GC */
  scm_gc_protect_object (scm_string_concat_2);
  scm_gc_protect_object (scm_string_concat_3);
  scm_gc_protect_object (scm_string_concat_multi);

  /* Protect integer parsing functions from GC */
  scm_gc_protect_object (scm_parse_integer_string);
  scm_gc_protect_object (scm_read_integer_guile);
  scm_gc_protect_object (scm_parse_emacs_number);
}

/* Lookup a color by name in a color map */
Lisp_Object
guile_lookup_color (Lisp_Object color_map, const char *color_name)
{
  if (!scm_is_true (scm_lookup_color_in_map))
    return Qnil;

  SCM result = SCM_CALL_2 (scm_lookup_color_in_map,
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

  SCM result = SCM_CALL_2 (scm_lookup_font_style,
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

  SCM result = SCM_CALL_2 (scm_lookup_in_alist_ci,
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

  SCM result = SCM_CALL_2 (scm_lookup_in_alist,
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

  SCM result = SCM_CALL_2 (scm_lookup_symbol_in_list,
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

  SCM result = SCM_CALL_1 (scm_parse_face_bool_attribute,
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

  SCM result = SCM_CALL_1 (scm_process_yesno_response,
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

  SCM result = SCM_CALL_3 (scm_filter_dbus_message,
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

  /* scm_is_special_buffer_name is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_is_special_buffer_name,
                           scm_from_utf8_string (SSDATA (buffer_name)));

  return scm_is_true (result);
}

/* Parse color specification and return RGB values */
Lisp_Object
guile_parse_color_spec (Lisp_Object color_spec)
{
  if (!scm_is_true (scm_parse_color_spec))
    return Qnil;

  if (!STRINGP (color_spec))
    return Qnil;

  /* scm_parse_color_spec is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_parse_color_spec,
                           scm_from_utf8_string (SSDATA (color_spec)));

  if (scm_is_false (result))
    return Qnil;

  /* Convert Scheme list (r g b) to Lisp list */
  if (scm_is_pair (result))
    {
      SCM r_scm = scm_car (result);
      SCM g_scm = scm_car (scm_cdr (result));
      SCM b_scm = scm_car (scm_cdr (scm_cdr (result)));

      if (scm_is_integer (r_scm) && scm_is_integer (g_scm) && scm_is_integer (b_scm))
        {
          int r = scm_to_int (r_scm);
          int g = scm_to_int (g_scm);
          int b = scm_to_int (b_scm);
          return list3i (r, g, b);
        }
    }

  return Qnil;
}

/* Validate color name */
bool
guile_validate_color_name (Lisp_Object color_name)
{
  if (!scm_is_true (scm_validate_color_name))
    return false;

  if (!STRINGP (color_name))
    return false;

  /* scm_validate_color_name is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_validate_color_name,
                           scm_from_utf8_string (SSDATA (color_name)));

  return scm_is_eq (result, scm_from_utf8_symbol ("valid"));
}

/* Check if string contains whitespace */
bool
guile_string_contains_whitespace (Lisp_Object str)
{
  if (scm_is_false (scm_string_contains_whitespace))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_string_contains_whitespace is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_string_contains_whitespace,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if frame name follows F<number> format */
bool
guile_is_frame_name_fnn_format (Lisp_Object name)
{
  if (!scm_is_true (scm_is_frame_name_fnn_format))
    return false;

  if (!STRINGP (name))
    return false;

  SCM result = SCM_CALL_1 (scm_is_frame_name_fnn_format,
                           scm_from_utf8_string (SSDATA (name)));

  return scm_is_true (result);
}

/* Validate XLFD font name format */
bool
guile_validate_xlfd_font_name (Lisp_Object name)
{
  if (!scm_is_true (scm_validate_xlfd_font_name))
    return false;

  if (!STRINGP (name))
    return false;

  SCM result = SCM_CALL_1 (scm_validate_xlfd_font_name,
                           scm_from_utf8_string (SSDATA (name)));

  return scm_is_eq (result, scm_from_utf8_symbol ("valid"));
}


/* String preprocessing functions */

/* Convert spaces to dashes in a string */
Lisp_Object
guile_string_spaces_to_dashes (Lisp_Object str)
{
  if (!scm_is_true (scm_string_spaces_to_dashes))
    return str; /* Fallback: return original string */

  if (!STRINGP (str))
    return str;

  SCM result = SCM_CALL_1 (scm_string_spaces_to_dashes,
                           scm_from_utf8_string (SSDATA (str)));

  if (scm_is_false (result))
    return str;

  /* Convert Scheme string back to Lisp string */
  if (scm_is_string (result))
    {
      char *c_str = scm_to_utf8_string (result);
      Lisp_Object lisp_str = make_string_from_utf8 (c_str, strlen (c_str));
      free (c_str);
      return lisp_str;
    }

  return str;
}

/* Trim leading whitespace from a string */
Lisp_Object
guile_string_trim_leading_whitespace (Lisp_Object str)
{
  if (!scm_is_true (scm_string_trim_leading_whitespace))
    return str; /* Fallback: return original string */

  if (!STRINGP (str))
    return str;

  SCM result = SCM_CALL_1 (scm_string_trim_leading_whitespace,
                           scm_from_utf8_string (SSDATA (str)));

  if (scm_is_false (result))
    return str;

  /* Convert Scheme string back to Lisp string */
  if (scm_is_string (result))
    {
      char *c_str = scm_to_utf8_string (result);
      Lisp_Object lisp_str = make_string_from_utf8 (c_str, strlen (c_str));
      free (c_str);
      return lisp_str;
    }

  return str;
}

/* Parse a number string with given base */
Lisp_Object
guile_parse_number_string (Lisp_Object str, int base)
{
  if (!scm_is_true (scm_parse_number_string))
    return make_fixnum (0); /* Fallback: return 0 */

  if (!STRINGP (str))
    return make_fixnum (0);

  SCM result = SCM_CALL_2 (scm_parse_number_string,
                           scm_from_utf8_string (SSDATA (str)),
                           scm_from_int (base));

  if (scm_is_false (result))
    return make_fixnum (0);

  /* Convert Scheme number to Lisp number */
  if (scm_is_integer (result))
    {
      long val = scm_to_long (result);
      return make_fixnum (val);
    }
  else if (scm_is_real (result))
    {
      double val = scm_to_double (result);
      return make_float (val);
    }

  return make_fixnum (0);
}

/* Validate string for copying operations */
bool
guile_validate_string_for_copying (Lisp_Object str)
{
  if (!scm_is_true (scm_validate_string_for_copying))
    return true; /* Fallback: assume valid */

  if (!STRINGP (str))
    return false;

  SCM result = SCM_CALL_1 (scm_validate_string_for_copying,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result) && scm_is_eq (result, scm_from_utf8_symbol ("valid"));
}

/* Prepare string for symbol creation */
Lisp_Object
guile_prepare_string_for_symbol (Lisp_Object str)
{
  if (!scm_is_true (scm_prepare_string_for_symbol))
    return str; /* Fallback: return original string */

  if (!STRINGP (str))
    return str;

  SCM result = SCM_CALL_1 (scm_prepare_string_for_symbol,
                           scm_from_utf8_string (SSDATA (str)));

  if (scm_is_false (result))
    return Qnil; /* Return nil if processing failed */

  /* Convert Scheme string back to Lisp string */
  if (scm_is_string (result))
    {
      char *c_str = scm_to_utf8_string (result);
      Lisp_Object lisp_str = make_string_from_utf8 (c_str, strlen (c_str));
      free (c_str);
      return lisp_str;
    }

  return str;
}


/* Check if filename has specific extension */
bool
guile_has_file_extension (Lisp_Object filename, const char *extension)
{
  if (!scm_is_true (scm_has_file_extension))
    return false;

  if (!STRINGP (filename))
    return false;

  SCM result = SCM_CALL_2 (scm_has_file_extension,
                           scm_from_utf8_string (SSDATA (filename)),
                           scm_from_utf8_string (extension));

  return scm_is_true (result);
}

/* Extract filename from full path */
Lisp_Object
guile_extract_filename_from_path (Lisp_Object path)
{
  if (!scm_is_true (scm_extract_filename_from_path))
    return path; /* Return original if Scheme not available */

  if (!STRINGP (path))
    return path;

  SCM result = SCM_CALL_1 (scm_extract_filename_from_path,
                           scm_from_utf8_string (SSDATA (path)));

  if (scm_is_string (result))
    {
      char *c_str = scm_to_utf8_string (result);
      Lisp_Object lisp_str = make_string_from_utf8 (c_str, strlen (c_str));
      free (c_str);
      return lisp_str;
    }

  return path;
}

/* Check if symbol matches modifier key string */
bool
guile_is_modifier_symbol (Lisp_Object symbol, const char *test_string)
{
  if (!scm_is_true (scm_is_modifier_symbol))
    return false;

  if (!SYMBOLP (symbol))
    return false;

  Lisp_Object name = SYMBOL_NAME (symbol);
  if (!STRINGP (name))
    return false;

  SCM result = SCM_CALL_2 (scm_is_modifier_symbol,
                           scm_from_utf8_string (SSDATA (name)),
                           scm_from_utf8_string (test_string));

  return scm_is_true (result);
}

/* Validate float format string */
bool
guile_validate_float_format_string (Lisp_Object format_str)
{
  if (!scm_is_true (scm_validate_float_format_string))
    return false;

  if (!STRINGP (format_str))
    return false;

  SCM result = SCM_CALL_1 (scm_validate_float_format_string,
                           scm_from_utf8_string (SSDATA (format_str)));

  return scm_is_eq (result, scm_from_utf8_symbol ("valid"));
}

/* Check if string has time format specifiers */
bool
guile_has_time_format_specifiers (Lisp_Object format_str)
{
  if (!scm_is_true (scm_has_time_format_specifiers))
    return false;

  if (!STRINGP (format_str))
    return false;

  SCM result = SCM_CALL_1 (scm_has_time_format_specifiers,
                           scm_from_utf8_string (SSDATA (format_str)));

  return scm_is_true (result);
}

/* Parse hex color string */
Lisp_Object
guile_parse_hex_color (Lisp_Object hex_str)
{
  if (!scm_is_true (scm_parse_hex_color))
    return Qnil;

  if (!STRINGP (hex_str))
    return Qnil;

  SCM result = SCM_CALL_1 (scm_parse_hex_color,
                           scm_from_utf8_string (SSDATA (hex_str)));

  if (scm_is_false (result))
    return Qnil;

  /* Convert Scheme list (r g b) to Lisp list */
  if (scm_is_pair (result))
    {
      SCM r_scm = scm_car (result);
      SCM g_scm = scm_car (scm_cdr (result));
      SCM b_scm = scm_car (scm_cdr (scm_cdr (result)));

      if (scm_is_integer (r_scm) && scm_is_integer (g_scm) && scm_is_integer (b_scm))
        {
          int r = scm_to_int (r_scm);
          int g = scm_to_int (g_scm);
          int b = scm_to_int (b_scm);
          return list3i (r, g, b);
        }
    }

  return Qnil;
}

/* Check if filename needs DOS to Unix conversion */
bool
guile_needs_filename_conversion (Lisp_Object filename)
{
  if (!scm_is_true (scm_needs_filename_conversion))
    return false;

  if (!STRINGP (filename))
    return false;

  SCM result = SCM_CALL_1 (scm_needs_filename_conversion,
                           scm_from_utf8_string (SSDATA (filename)));

  return scm_is_true (result);
}

/* Check if filename is UTF-8 encoded */
bool
guile_is_utf8_filename (Lisp_Object filename)
{
  if (!scm_is_true (scm_is_utf8_filename))
    return true; /* Assume UTF-8 if Scheme not available */

  if (!STRINGP (filename))
    return false;

  SCM result = SCM_CALL_1 (scm_is_utf8_filename,
                           scm_from_utf8_string (SSDATA (filename)));

  return scm_is_true (result);
}

/* Check if string is safe for C string copying */
bool
guile_is_safe_for_c_string_copy (Lisp_Object str)
{
  if (!scm_is_true (scm_is_safe_for_c_string_copy))
    return true; /* Assume safe if Scheme not available */

  if (!STRINGP (str))
    return false;

  SCM result = SCM_CALL_1 (scm_is_safe_for_c_string_copy,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if string looks like network address */
bool
guile_looks_like_network_address (Lisp_Object addr_str)
{
  if (!scm_is_true (scm_looks_like_network_address))
    return false;

  if (!STRINGP (addr_str))
    return false;

  SCM result = SCM_CALL_1 (scm_looks_like_network_address,
                           scm_from_utf8_string (SSDATA (addr_str)));

  return scm_is_true (result);
}

/* Path/Filename operation bridge functions */

/* Check if path is absolute (cross-platform) */
bool
guile_is_absolute_path (Lisp_Object path)
{
  if (!scm_is_true (scm_is_absolute_path))
    return false;

  if (!STRINGP (path))
    return false;

  /* scm_is_absolute_path is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_is_absolute_path,
                           scm_from_utf8_string (SSDATA (path)));

  return scm_is_true (result);
}

/* Check if path ends with directory separator */
bool
guile_ends_with_directory_separator (Lisp_Object path)
{
  if (!scm_is_true (scm_ends_with_directory_separator))
    return false;

  if (!STRINGP (path))
    return false;

  /* scm_ends_with_directory_separator is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_ends_with_directory_separator,
                           scm_from_utf8_string (SSDATA (path)));

  return scm_is_true (result);
}

/* Normalize path separators */
Lisp_Object
guile_normalize_path_separators (Lisp_Object path)
{
  if (!scm_is_true (scm_normalize_path_separators))
    return path; /* Return original if Scheme not available */

  if (!STRINGP (path))
    return path;

  /* scm_normalize_path_separators is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_normalize_path_separators,
                           scm_from_utf8_string (SSDATA (path)));

  if (scm_is_string (result))
    {
      char *c_str = scm_to_utf8_string (result);
      Lisp_Object lisp_str = make_string_from_utf8 (c_str, strlen (c_str));
      free (c_str);
      return lisp_str;
    }

  return path;
}

/* Check if string is empty */
bool
guile_string_empty (Lisp_Object str)
{
  if (!scm_is_true (scm_string_empty))
    return false;

  if (!STRINGP (str))
    return false;

  SCM result = SCM_CALL_1 (scm_string_empty,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if path has directory traversal patterns */
bool
guile_has_directory_traversal (Lisp_Object path)
{
  if (!scm_is_true (scm_has_directory_traversal))
    return false;

  if (!STRINGP (path))
    return false;

  SCM result = SCM_CALL_1 (scm_has_directory_traversal,
                           scm_from_utf8_string (SSDATA (path)));

  return scm_is_true (result);
}

/* Get file extension from path */
Lisp_Object
guile_get_file_extension (Lisp_Object path)
{
  if (!scm_is_true (scm_get_file_extension))
    return build_string (""); /* Return empty string if Scheme not available */

  if (!STRINGP (path))
    return build_string ("");

  SCM result = SCM_CALL_1 (scm_get_file_extension,
                           scm_from_utf8_string (SSDATA (path)));

  if (scm_is_string (result))
    {
      char *c_str = scm_to_utf8_string (result);
      Lisp_Object lisp_str = make_string_from_utf8 (c_str, strlen (c_str));
      free (c_str);
      return lisp_str;
    }

  return build_string ("");
}

/* Check if path starts with specific prefix */
bool
guile_path_starts_with (Lisp_Object path, const char *prefix)
{
  if (!scm_is_true (scm_path_starts_with))
    return false;

  if (!STRINGP (path))
    return false;

  /* scm_path_starts_with is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_2 (scm_path_starts_with,
                           scm_from_utf8_string (SSDATA (path)),
                           scm_from_utf8_string (prefix));

  return scm_is_true (result);
}

/* Simple string validation bridge functions */

/* Check if string has exactly one character */
bool
guile_string_single_char (Lisp_Object str)
{
  if (!scm_is_true (scm_string_single_char))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_string_single_char is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_string_single_char,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if string starts with space character */
bool
guile_string_starts_with_space (Lisp_Object str)
{
  if (!scm_is_true (scm_string_starts_with_space))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_string_starts_with_space is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_string_starts_with_space,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if string contains only ASCII characters */
bool
guile_string_ascii_only (Lisp_Object str)
{
  if (!scm_is_true (scm_string_ascii_only))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_string_ascii_only is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_string_ascii_only,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if string is a valid symbol name */
bool
guile_valid_symbol_name (Lisp_Object str)
{
  if (!scm_is_true (scm_valid_symbol_name))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_valid_symbol_name is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_valid_symbol_name,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if string looks like a number */
bool
guile_string_numeric (Lisp_Object str)
{
  if (!scm_is_true (scm_string_numeric))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_string_numeric is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_string_numeric,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if buffer name represents a special buffer */
bool
guile_special_buffer_name (Lisp_Object buffer_name)
{
  if (!scm_is_true (scm_special_buffer_name))
    return false;

  if (!STRINGP (buffer_name))
    return false;

  /* scm_special_buffer_name is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_special_buffer_name,
                           scm_from_utf8_string (SSDATA (buffer_name)));

  return scm_is_true (result);
}

/* Check if string starts with specific character */
bool
guile_string_starts_with_char (Lisp_Object str, int character)
{
  if (!scm_is_true (scm_string_starts_with_char))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_string_starts_with_char is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_2 (scm_string_starts_with_char,
                           scm_from_utf8_string (SSDATA (str)),
                           scm_from_int (character));

  return scm_is_true (result);
}

/* File extension and type checking bridge functions */

/* Check if filename has specific extension */
bool
guile_has_file_extension_new (Lisp_Object filename, const char *extension)
{
  if (!scm_is_true (scm_has_file_extension))
    return false;

  if (!STRINGP (filename))
    return false;

  /* scm_has_file_extension is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_2 (scm_has_file_extension,
                           scm_from_utf8_string (SSDATA (filename)),
                           scm_from_utf8_string (extension));

  return scm_is_true (result);
}

/* Check if filename is a source code file */
bool
guile_source_code_file (Lisp_Object filename)
{
  if (!scm_is_true (scm_source_code_file))
    return false;

  if (!STRINGP (filename))
    return false;

  /* scm_source_code_file is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_source_code_file,
                           scm_from_utf8_string (SSDATA (filename)));

  return scm_is_true (result);
}

/* Check if filename is an image file */
bool
guile_image_file (Lisp_Object filename)
{
  if (!scm_is_true (scm_image_file))
    return false;

  if (!STRINGP (filename))
    return false;

  /* scm_image_file is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_image_file,
                           scm_from_utf8_string (SSDATA (filename)));

  return scm_is_true (result);
}

/* Font and color validation bridge functions */

/* Check if string looks like a hex color */
bool
guile_hex_color_string (Lisp_Object str)
{
  if (!scm_is_true (scm_hex_color_string))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_hex_color_string is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_hex_color_string,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if string is a named color */
bool
guile_named_color (Lisp_Object color_name)
{
  if (!scm_is_true (scm_named_color))
    return false;

  if (!STRINGP (color_name))
    return false;

  /* scm_named_color is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_named_color,
                           scm_from_utf8_string (SSDATA (color_name)));

  return scm_is_true (result);
}

/* Validate XLFD font name format */
bool
guile_valid_xlfd_font_name_new (Lisp_Object font_name)
{
  if (!scm_is_true (scm_valid_xlfd_font_name))
    return false;

  if (!STRINGP (font_name))
    return false;

  /* scm_valid_xlfd_font_name is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_valid_xlfd_font_name,
                           scm_from_utf8_string (SSDATA (font_name)));

  return scm_is_true (result);
}

/* Check if string looks like a font family name */
bool
guile_font_family_name (Lisp_Object name)
{
  if (!scm_is_true (scm_font_family_name))
    return false;

  if (!STRINGP (name))
    return false;

  /* scm_font_family_name is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_font_family_name,
                           scm_from_utf8_string (SSDATA (name)));

  return scm_is_true (result);
}

/* Network and URL validation bridge functions */

/* Check if string looks like a URL */
bool
guile_url_string (Lisp_Object str)
{
  if (!scm_is_true (scm_url_string))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_url_string is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_url_string,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Additional missing bridge functions */

/* Check if string is an email address */
bool
guile_email_address (Lisp_Object addr_str)
{
  if (!scm_is_true (scm_email_address))
    return false;

  if (!STRINGP (addr_str))
    return false;

  /* scm_email_address is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_email_address,
                           scm_from_utf8_string (SSDATA (addr_str)));

  return scm_is_true (result);
}

/* Check if string is an IP address */
bool
guile_ip_address (Lisp_Object addr_str)
{
  if (!scm_is_true (scm_ip_address))
    return false;

  if (!STRINGP (addr_str))
    return false;

  /* scm_ip_address is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_ip_address,
                           scm_from_utf8_string (SSDATA (addr_str)));

  return scm_is_true (result);
}

/* Check if filename is a config file */
bool
guile_config_file (Lisp_Object filename)
{
  if (!scm_is_true (scm_config_file))
    return false;

  if (!STRINGP (filename))
    return false;

  /* scm_config_file is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_config_file,
                           scm_from_utf8_string (SSDATA (filename)));

  return scm_is_true (result);
}

/* Extract file extension from filename */
Lisp_Object
guile_extract_file_extension (Lisp_Object filename)
{
  if (!scm_is_true (scm_extract_file_extension))
    return build_string (""); /* Return empty string if Scheme not available */

  if (!STRINGP (filename))
    return build_string ("");

  /* scm_extract_file_extension is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_extract_file_extension,
                           scm_from_utf8_string (SSDATA (filename)));

  if (scm_is_string (result))
    {
      char *c_str = scm_to_utf8_string (result);
      Lisp_Object lisp_str = make_string_from_utf8 (c_str, strlen (c_str));
      free (c_str);
      return lisp_str;
    }

  return build_string ("");
}

/* Check if string is an RGB color string */
bool
guile_rgb_color_string (Lisp_Object str)
{
  if (!scm_is_true (scm_rgb_color_string))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_rgb_color_string is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_rgb_color_string,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Additional string validation functions */

/* Check if string needs escaping */
bool
guile_string_needs_escaping (Lisp_Object str)
{
  if (!scm_is_true (scm_string_needs_escaping))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_string_needs_escaping is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_string_needs_escaping,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if strings are equal ignoring case */
bool
guile_string_equal_ignore_case (Lisp_Object str1, Lisp_Object str2)
{
  if (!scm_is_true (scm_string_equal_ignore_case))
    return false;

  if (!STRINGP (str1) || !STRINGP (str2))
    return false;

  /* scm_string_equal_ignore_case is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_2 (scm_string_equal_ignore_case,
                           scm_from_utf8_string (SSDATA (str1)),
                           scm_from_utf8_string (SSDATA (str2)));

  return scm_is_true (result);
}

/* Check if string ends with specific character */
bool
guile_string_ends_with_char (Lisp_Object str, int character)
{
  if (!scm_is_true (scm_string_ends_with_char))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_string_ends_with_char is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_2 (scm_string_ends_with_char,
                           scm_from_utf8_string (SSDATA (str)),
                           scm_from_int (character));

  return scm_is_true (result);
}

/* Check if string contains only whitespace */
bool
guile_string_whitespace_only (Lisp_Object str)
{
  if (!scm_is_true (scm_string_whitespace_only))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_string_whitespace_only is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_string_whitespace_only,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Check if string is a valid identifier */
bool
guile_valid_identifier (Lisp_Object str)
{
  if (!scm_is_true (scm_valid_identifier))
    return false;

  if (!STRINGP (str))
    return false;

  /* scm_valid_identifier is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_valid_identifier,
                           scm_from_utf8_string (SSDATA (str)));

  return scm_is_true (result);
}

/* Registry to script mapping lookup */
Lisp_Object
guile_lookup_registry_to_script (Lisp_Object reg_to_script_alist, const char *registry_str)
{
  if (!scm_is_true (scm_lookup_registry_to_script))
    return Qnil;

  SCM result = SCM_CALL_2 (scm_lookup_registry_to_script,
                           reg_to_script_alist,
                           scm_from_utf8_string (registry_str));

  if (scm_is_false (result))
    return Qnil;

  return result;
}

/* Font name parsing for size extraction */
Lisp_Object
guile_parse_font_name_with_size (Lisp_Object font_name, double current_size)
{
  if (!scm_is_true (scm_parse_font_name_with_size))
    return Qnil;

  if (!STRINGP (font_name))
    return Qnil;

  SCM size_scm = (current_size > 0) ? scm_from_double (current_size) : SCM_BOOL_F;

  SCM result = SCM_CALL_2 (scm_parse_font_name_with_size,
                           scm_from_utf8_string (SSDATA (font_name)),
                           size_scm);

  if (scm_is_false (result))
    return Qnil;

  return result;
}

/* String operations without properties using Scheme */
Lisp_Object
guile_substring_no_properties (Lisp_Object string, Lisp_Object start, Lisp_Object end)
{
  if (!scm_is_true (scm_substring_no_properties_scheme))
    return Qnil;

  if (!STRINGP (string))
    return Qnil;

  /* Enhanced type safety - check for valid fixnums */
  SCM start_scm = NILP (start) ? SCM_BOOL_F :
    (FIXNUMP (start) ? scm_from_int (XFIXNUM (start)) : SCM_BOOL_F);
  SCM end_scm = NILP (end) ? SCM_BOOL_F :
    (FIXNUMP (end) ? scm_from_int (XFIXNUM (end)) : SCM_BOOL_F);

  /* scm_substring_no_properties_scheme is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_3 (scm_substring_no_properties_scheme, string, start_scm, end_scm);

  if (scm_is_false (result))
    return build_string ("");

  return result;
}

/* File path operations using Scheme implementations */

/* Check if path is absolute */
bool
guile_file_path_absolute_p (Lisp_Object path)
{
  if (!scm_is_true (scm_file_path_absolute_p))
    return false;

  if (!STRINGP (path))
    return false;

  /* scm_file_path_absolute_p is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_file_path_absolute_p, path);
  return scm_is_true (result);
}

/* Extract directory component from path */
Lisp_Object
guile_file_path_directory (Lisp_Object path)
{
  if (!scm_is_true (scm_file_path_directory))
    return Qnil;

  if (!STRINGP (path))
    return Qnil;

  /* scm_file_path_directory is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_file_path_directory, path);

  if (scm_is_false (result))
    return build_string ("");

  return result;
}

/* Extract filename component from path */
Lisp_Object
guile_file_path_nondirectory (Lisp_Object path)
{
  if (!scm_is_true (scm_file_path_nondirectory))
    return Qnil;

  if (!STRINGP (path))
    return Qnil;

  /* scm_file_path_nondirectory is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_file_path_nondirectory, path);

  if (scm_is_false (result))
    return build_string ("");

  return result;
}

/* Check if path is safe (no directory traversal) */
bool
guile_file_path_safe_p (Lisp_Object path)
{
  if (!scm_is_true (scm_file_path_safe_p))
    return false;

  if (!STRINGP (path))
    return false;

  /* scm_file_path_safe_p is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_file_path_safe_p, path);
  return scm_is_true (result);
}

/* String concatenation operations using Scheme implementations */

/* Concatenate two strings */
Lisp_Object
guile_string_concat_2 (Lisp_Object s1, Lisp_Object s2)
{
  if (!scm_is_true (scm_string_concat_2))
    return Qnil;

  /* scm_string_concat_2 is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_2 (scm_string_concat_2, s1, s2);

  if (scm_is_false (result))
    return build_string ("");

  return result;
}

/* Concatenate three strings */
Lisp_Object
guile_string_concat_3 (Lisp_Object s1, Lisp_Object s2, Lisp_Object s3)
{
  if (!scm_is_true (scm_string_concat_3))
    return Qnil;

  /* scm_string_concat_3 is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_3 (scm_string_concat_3, s1, s2, s3);

  if (scm_is_false (result))
    return build_string ("");

  return result;
}

/* Concatenate multiple strings from a list */
Lisp_Object
guile_string_concat_multi (Lisp_Object string_list)
{
  if (!scm_is_true (scm_string_concat_multi))
    return Qnil;

  /* scm_string_concat_multi is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_string_concat_multi, string_list);

  if (scm_is_false (result))
    return build_string ("");

  return result;
}

/* Integer parsing operations using Scheme implementations */

/* Parse integer from string with radix */
Lisp_Object
guile_parse_integer_string (Lisp_Object str, int radix)
{
  if (!scm_is_true (scm_parse_integer_string))
    return Qnil;

  if (!STRINGP (str))
    return Qnil;

  /* scm_parse_integer_string is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_2 (scm_parse_integer_string, str, scm_from_int (radix));

  if (scm_is_false (result))
    return Qnil;

  return result;
}

/* Read integer using Guile native reader */
Lisp_Object
guile_read_integer_guile (Lisp_Object input_string)
{
  if (!scm_is_true (scm_read_integer_guile))
    return Qnil;

  if (!STRINGP (input_string))
    return Qnil;

  /* scm_read_integer_guile is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_read_integer_guile, input_string);

  if (scm_is_false (result))
    return Qnil;

  return result;
}

/* Parse Emacs number format (complete number parsing) */
Lisp_Object
guile_parse_emacs_number (Lisp_Object str)
{
  if (!scm_is_true (scm_parse_emacs_number))
    return Qnil;

  if (!STRINGP (str))
    return Qnil;

  /* scm_parse_emacs_number is now the actual procedure (not a variable) */
  SCM result = SCM_CALL_1 (scm_parse_emacs_number, str);

  if (scm_is_false (result))
    return Qnil;

  return result;
}
