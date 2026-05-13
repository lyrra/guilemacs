/* Guile utilities.

Copyright (C) 2013 Free Software Foundation, Inc.

This file is part of GNU Emacs.

GNU Emacs is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

GNU Emacs is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.  */

#include <config.h>
#include "lisp.h"
#include "guile.h"

struct elisp_functions_ptr elisp_functions_ptr;

scm_t_bits c_closure_tag;
scm_t_bits kboard_tag;

typedef SCM (*c_closure_0_t) (void *);
typedef SCM (*c_closure_1_t) (void *, SCM);
typedef SCM (*c_closure_2_t) (void *, SCM, SCM);
typedef SCM (*c_closure_3_t) (void *, SCM, SCM, SCM);
typedef SCM (*c_closure_4_t) (void *, SCM, SCM, SCM, SCM);
typedef SCM (*c_closure_5_t) (void *, SCM, SCM, SCM, SCM, SCM);
typedef SCM (*c_closure_6_t) (void *, SCM, SCM, SCM, SCM, SCM, SCM);
typedef SCM (*c_closure_7_t) (void *, SCM, SCM, SCM, SCM, SCM, SCM, SCM);

SCM
make_c_closure (SCM (*func) (), void *data, int req, int opt)
{
  SCM smob;

  if (req > 3 || opt > 1)
    emacs_abort ();

  SCM_NEWSMOB2 (smob, c_closure_tag, func, data);
  SCM_SET_SMOB_FLAGS (smob, req | (opt << 2));
  return smob;
}

static SCM
apply_c_closure (SCM c_closure, SCM args)
{
  int req, opt;
  SCM cargs[7];
  long nargs = scm_to_long (scm_length (args));
  scm_t_bits flags = SCM_SMOB_FLAGS (c_closure);
  scm_t_bits func = SCM_SMOB_DATA (c_closure);
  void *data = (void *) SCM_SMOB_DATA_2 (c_closure);

  req = flags & 3;
  opt = (flags >> 2) & 1;

  for (int i = 0; i < req + opt; i++)
    {
      if (scm_is_pair (args))
        {
          cargs[i] = scm_car (args);
          args = scm_cdr (args);
        }
      else if (opt)
        {
          cargs[i] = SCM_UNDEFINED;
        }
      else
        scm_wrong_num_args (c_closure);
    }

  switch (req + opt)
    {
    case 0: return ((c_closure_0_t) func) (data);
    case 1: return ((c_closure_1_t) func) (data, cargs[0]);
    case 2: return ((c_closure_2_t) func) (data, cargs[0], cargs[1]);
    case 3: return ((c_closure_3_t) func) (data, cargs[0], cargs[1], cargs[2]);
    case 4: return ((c_closure_4_t) func) (data, cargs[0], cargs[1], cargs[2], cargs[3]);
    default:
      emacs_abort ();
    }
}

void
init_elisp_functions (void)
{
  SCM emacs_list = scm_c_resolve_module ("emacs list");

  elisp_functions_ptr.f_car = scm_c_module_lookup (emacs_list, "elisp-car");
  elisp_functions_ptr.f_cdr = scm_c_module_lookup (emacs_list, "elisp-cdr");
}

void
init_guile (void)
{
  init_elisp_functions();
  c_closure_tag = scm_make_smob_type ("c-closure", 0);
  scm_set_smob_apply (c_closure_tag, apply_c_closure, 0, 0, 1);

  /* M2: foreign-object wrapper around KBOARD*.  See
     mod/emacs/kboard.scm and docs/keyboard.org §M2.  The smob holds an
     opaque KBOARD* in SMOB_DATA; the C-side kboard struct remains
     owned by all_kboards and freed by delete_kboard, so no finalizer
     is needed.  */
  kboard_tag = scm_make_smob_type ("kboard", 0);
}

/*
 * debugging
 */

/* Dump all fboundp symbols to a file.
   Call from GDB: call debug_dump_symbol_functions("/tmp/sym.txt") */
static FILE *debug_dump_file;

static SCM
debug_dump_one_symbol (SCM sym)
{
  SCM sym_name_fn = scm_c_public_ref ("emacs-elisp runtime", "symbol-name");
  SCM sym_fn_fn = scm_c_public_ref ("emacs-elisp runtime", "symbol-function");
  SCM fboundp_fn = scm_c_public_ref ("emacs-elisp runtime", "fboundp");

  if (scm_is_false (scm_call_1 (fboundp_fn, sym)))
    return SCM_UNSPECIFIED;

  SCM name_str = scm_call_1 (sym_name_fn, sym);
  SCM func = scm_call_1 (sym_fn_fn, sym);
  char *name = scm_to_utf8_string (name_str);

  if (scm_is_true (scm_procedure_p (func)))
    {
      SCM pname = (scm_procedure_name) (func);
      if (scm_is_true (pname))
        {
          char *pn = scm_to_utf8_string (scm_symbol_to_string (pname));
          fprintf (debug_dump_file, "%-40s -> %p  [%s]\n",
                   name, (void *) SCM_UNPACK (func), pn);
          free (pn);
        }
      else
        fprintf (debug_dump_file, "%-40s -> %p  [anonymous]\n",
                 name, (void *) SCM_UNPACK (func));
    }
  else
    fprintf (debug_dump_file, "%-40s -> %p  [non-procedure]\n",
             name, (void *) SCM_UNPACK (func));

  free (name);
  return SCM_UNSPECIFIED;
}

void
debug_dump_symbol_functions (const char *filename)
{
  debug_dump_file = fopen (filename, "w");
  if (!debug_dump_file)
    {
      fprintf (stderr, "Cannot open %s\n", filename);
      return;
    }

  SCM for_each_fn = scm_c_public_ref ("emacs-elisp runtime",
                                       "for-each-elisp-symbol");
  SCM callback = scm_c_make_gsubr ("debug-dump-cb", 1, 0, 0,
                                    (scm_t_subr) debug_dump_one_symbol);
  scm_call_1 (for_each_fn, callback);

  fclose (debug_dump_file);
  debug_dump_file = NULL;
  fprintf (stderr, "Dumped to %s\n", filename);
}

/* Call from GDB: call debug_scm_proc_name(fn) */
void
debug_scm_proc_name (SCM fn)
{
  SCM name = scm_procedure_name (fn);
  if (scm_is_true (name))
    fprintf (stderr, "%s\n", scm_to_utf8_string (scm_symbol_to_string (name)));
  else
    fprintf (stderr, "(anonymous)\n");
}

/* Call from GDB: call debug_guile_backtrace()
   Prints the Guile VM stack (Scheme + gsubr frames). */
void
debug_guile_backtrace (void)
{
  SCM stack = scm_make_stack (SCM_BOOL_T, SCM_EOL);
  SCM port = scm_current_error_port ();
  scm_display_backtrace (stack, port, SCM_BOOL_F, SCM_BOOL_F);
  scm_force_output (port);
}

/* Call from GDB: call debug_scm_print(obj)
   Print any SCM value to stderr. */
void
debug_scm_print (SCM obj)
{
  SCM port = scm_current_error_port ();
  scm_write (obj, port);
  scm_newline (port);
  scm_force_output (port);
}

/* Call from GDB: call debug_lisp_print(obj)
   Print a Lisp_Object using Emacs' printer. */
void
debug_lisp_print (Lisp_Object obj)
{
  Fprin1 (obj, Qexternal_debugging_output, Qnil);
  fprintf (stderr, "\n");
}

/* Call from GDB: call debug_scm_value(obj)
   Identify the type and value of an SCM. */
void
debug_scm_value (SCM obj)
{
  if (scm_is_false (obj))
    fprintf (stderr, "#f\n");
  else if (scm_is_null (obj))
    fprintf (stderr, "()\n");
  else if (scm_is_true (scm_symbol_p (obj)))
    fprintf (stderr, "symbol: %s\n",
             scm_to_utf8_string (scm_symbol_to_string (obj)));
  else if (scm_is_string (obj))
    fprintf (stderr, "string: \"%s\"\n", scm_to_utf8_string (obj));
  else if (scm_is_integer (obj))
    fprintf (stderr, "integer: %ld\n", scm_to_long (obj));
  else if (scm_is_true (scm_procedure_p (obj)))
    {
      fprintf (stderr, "procedure: %p", (void *) SCM_UNPACK (obj));
      SCM name = scm_procedure_name (obj);
      if (scm_is_true (name))
        fprintf (stderr, " [%s]",
                 scm_to_utf8_string (scm_symbol_to_string (name)));
      fprintf (stderr, "\n");
    }
  else if (scm_is_pair (obj))
    {
      fprintf (stderr, "pair: ");
      debug_scm_print (obj);
    }
  else
    fprintf (stderr, "SCM %p (use debug_scm_print for details)\n",
             (void *) SCM_UNPACK (obj));
}
