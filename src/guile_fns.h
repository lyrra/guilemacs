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

#endif /* GUILE_LOOKUPS_H */
