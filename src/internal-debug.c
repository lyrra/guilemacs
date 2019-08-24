

/*
 * Emacs development debugging
 * These functions are only useful to track the source-backtrace
 * and such during debugging, and with GDB running.
 */

#include <config.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/file.h>
#include <errno.h>
#include <fcntl.h>

#include "lisp.h"

/*** Breakpoints ***/

void
emacs_gdb_breakpoint (char *desc)
{
  fprintf(stderr, "Welcome! Emacs gdb breakpoint is hit: %s\n", desc);
}

void
emacs_gdb_breakpoint_value (void *item)
{
  fprintf(stderr, "Welcome! Emacs gdb breakpoint is hit, item=%lx\n", item);
}

DEFUN ("gdb-breakpoint", Fgdb_breakpoint, Sgdb_breakpoint, 1, 1, 0,
       doc: /* in gdb, set a breakpoint on emacs_gdb_breakpoint, and call (gdb-breakpoint) from your elisp code. */)
  (Lisp_Object desc)
{
  CHECK_STRING (desc);
  emacs_gdb_breakpoint(SSDATA(desc));
  return Qnil;
}

DEFUN ("gdb-breakpoint-value", Fgdb_breakpoint_value, Sgdb_breakpoint_value, 1, 1, 0,
       doc: /* in gdb, set a breakpoint on emacs_gdb_breakpoint_value, and call (gdb-breakpoint-value) from your elisp code. */)
  (Lisp_Object item)
{
  emacs_gdb_breakpoint_value(item);
  return Qnil;
}


/*** printf-debugging ***/
