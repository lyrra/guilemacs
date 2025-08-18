/* guile_lookups.h - Interface to Guile lookup functions */

#ifndef GUILE_LOOKUPS_H
#define GUILE_LOOKUPS_H

#include "lisp.h"
#include <libguile.h>

/* Initialize the Guile lookup functions module */
extern void init_guile_fns (void);

/* Lookup a color by name in a color map */
extern Lisp_Object guile_lookup_color (Lisp_Object color_map, const char *color_name);

/* Lookup a font style in a font style table */
extern Lisp_Object guile_lookup_font_style (Lisp_Object table, const char *style_name);

/* Lookup in an alist with case-insensitive comparison */
extern Lisp_Object guile_lookup_alist_ci (Lisp_Object alist, const char *key);

/* Lookup in an alist with case-sensitive comparison */
extern Lisp_Object guile_lookup_alist (Lisp_Object alist, const char *key);

/* Check if a symbol name exists in a list */
extern bool guile_lookup_symbol_in_list (Lisp_Object list, const char *name);

/* Parse face boolean attribute - returns 1 for true, -1 for false, 0 for unknown */
extern int guile_parse_face_bool_attribute (Lisp_Object attr_string);

/* Process yes/no response - returns 1 for yes, 0 for no, -1 for invalid */
extern int guile_process_yesno_response (Lisp_Object response_string);

/* Filter DBus message based on interface and member patterns */
extern bool guile_filter_dbus_message (Lisp_Object message, Lisp_Object interface_pattern, Lisp_Object member_pattern);

/* Check if buffer name represents a special (internal) buffer */
extern bool guile_is_special_buffer_name (Lisp_Object buffer_name);

/* Parse color specification and return RGB values as Lisp list */
extern Lisp_Object guile_parse_color_spec (Lisp_Object color_spec);

/* Validate if color name is recognizable */
extern bool guile_validate_color_name (Lisp_Object color_name);

/* Check if string contains whitespace characters */
extern bool guile_string_contains_whitespace (Lisp_Object str);

/* Check if frame name follows F<number> format */
extern bool guile_is_frame_name_fnn_format (Lisp_Object name);

/* Validate XLFD font name format */
extern bool guile_validate_xlfd_font_name (Lisp_Object name);

/* Check if path is absolute */
extern bool guile_is_absolute_path (Lisp_Object path);

/* Check if path contains directory traversal patterns */
extern bool guile_has_directory_traversal (Lisp_Object path);

/* String preprocessing functions */

/* Convert spaces to dashes in a string */
extern Lisp_Object guile_string_spaces_to_dashes (Lisp_Object str);

/* Trim leading whitespace from a string */
extern Lisp_Object guile_string_trim_leading_whitespace (Lisp_Object str);

/* Parse a number string with given base */
extern Lisp_Object guile_parse_number_string (Lisp_Object str, int base);

/* Validate string for copying operations */
extern bool guile_validate_string_for_copying (Lisp_Object str);

/* Prepare string for symbol creation */
extern Lisp_Object guile_prepare_string_for_symbol (Lisp_Object str);

/* New SSDATA hoisting functions */

/* Check if filename has specific extension */
extern bool guile_has_file_extension (Lisp_Object filename, const char *extension);

/* Extract filename from full path */
extern Lisp_Object guile_extract_filename_from_path (Lisp_Object path);

/* Check if symbol matches modifier key string */
extern bool guile_is_modifier_symbol (Lisp_Object symbol, const char *test_string);

/* Validate float format string */
extern bool guile_validate_float_format_string (Lisp_Object format_str);

/* Check if string has time format specifiers */
extern bool guile_has_time_format_specifiers (Lisp_Object format_str);

/* Parse hex color string and return RGB values as Lisp list */
extern Lisp_Object guile_parse_hex_color (Lisp_Object hex_str);

/* Check if filename needs DOS to Unix conversion */
extern bool guile_needs_filename_conversion (Lisp_Object filename);

/* Check if filename is UTF-8 encoded */
extern bool guile_is_utf8_filename (Lisp_Object filename);

/* Check if string is safe for C string copying */
extern bool guile_is_safe_for_c_string_copy (Lisp_Object str);

/* Check if string looks like network address */
extern bool guile_looks_like_network_address (Lisp_Object addr_str);

/* Path/Filename operation functions */

/* Check if path is absolute (cross-platform) */
extern bool guile_is_absolute_path (Lisp_Object path);

/* Check if path ends with directory separator */
extern bool guile_ends_with_directory_separator (Lisp_Object path);

/* Normalize path separators (convert / to \ on Windows) */
extern Lisp_Object guile_normalize_path_separators (Lisp_Object path);

/* Check if string is empty */
extern bool guile_string_empty (Lisp_Object str);

/* Check if path has directory traversal patterns */
extern bool guile_has_directory_traversal (Lisp_Object path);

/* Get file extension from path */
extern Lisp_Object guile_get_file_extension (Lisp_Object path);

/* Check if path starts with specific prefix */
extern bool guile_path_starts_with (Lisp_Object path, const char *prefix);

/* Simple string validation functions */

/* Check if string has exactly one character */
extern bool guile_string_single_char (Lisp_Object str);

/* Check if string starts with space character */
extern bool guile_string_starts_with_space (Lisp_Object str);

/* Check if string contains only ASCII characters */
extern bool guile_string_ascii_only (Lisp_Object str);

/* Check if string is a valid symbol name */
extern bool guile_valid_symbol_name (Lisp_Object str);

/* Check if string looks like a number */
extern bool guile_string_numeric (Lisp_Object str);

/* Check if buffer name represents a special buffer */
extern bool guile_special_buffer_name (Lisp_Object buffer_name);

/* Check if string starts with specific character */
extern bool guile_string_starts_with_char (Lisp_Object str, int character);

/* File extension and type checking functions */

/* Check if filename has specific extension */
extern bool guile_has_file_extension_new (Lisp_Object filename, const char *extension);

/* Check if filename is a source code file */
extern bool guile_source_code_file (Lisp_Object filename);

/* Check if filename is an image file */
extern bool guile_image_file (Lisp_Object filename);

/* Font and color validation functions */

/* Check if string looks like a hex color */
extern bool guile_hex_color_string (Lisp_Object str);

/* Check if string is a named color */
extern bool guile_named_color (Lisp_Object color_name);

/* Validate XLFD font name format */
extern bool guile_valid_xlfd_font_name_new (Lisp_Object font_name);

/* Check if string looks like a font family name */
extern bool guile_font_family_name (Lisp_Object name);

/* Network and URL validation functions */

/* Check if string looks like a URL */
extern bool guile_url_string (Lisp_Object str);

#endif /* GUILE_LOOKUPS_H */
