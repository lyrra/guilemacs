/* Primitive operations on Lisp data types for GNU Emacs Lisp interpreter.
   Copyright (C) 1985-1986, 1988, 1993-1995, 1997-2025 Free Software
   Foundation, Inc.

This file is part of GNU Emacs.

GNU Emacs is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or (at
your option) any later version.

GNU Emacs is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GNU Emacs.  If not, see <https://www.gnu.org/licenses/>.  */


#include <config.h>

#include <math.h>
#include <stdio.h>

#include <intprops.h>

#include "lisp.h"
#include "guile.h"
#include "guile_fns.h"
#include "puresize.h"
#include "character.h"
#include "buffer.h"
#include "keyboard.h"
#include "process.h"
#include "frame.h"
#include "keymap.h"

int
value_cmp_scm (Lisp_Object a, Lisp_Object b);

#define WRAP1(cfn, lfn) \
  Lisp_Object cfn (Lisp_Object a) \
  { return call1 (cfn ## _sym, a); }

#define WRAP2(cfn, lfn) Lisp_Object cfn (Lisp_Object a, Lisp_Object b) { return call2 (intern (lfn), a, b); }

#define SLOWWRAP1(cfn, lfn) \
  Lisp_Object cfn (Lisp_Object a) \
  { return call1 (intern (lfn), a); }

static void swap_in_symval_forwarding (sym_t, struct Lisp_Buffer_Local_Value *);

static bool
BOOLFWDP (lispfwd a)
{
  return XFWDTYPE (a) == Lisp_Fwd_Bool;
}
static bool
INTFWDP (lispfwd a)
{
  return XFWDTYPE (a) == Lisp_Fwd_Int;
}
static bool
OBJFWDP (lispfwd a)
{
  return XFWDTYPE (a) == Lisp_Fwd_Obj;
}

static struct Lisp_Boolfwd const *
XBOOLFWD (lispfwd a)
{
  eassert (BOOLFWDP (a));
  return a.fwdptr;
}
static struct Lisp_Kboard_Objfwd const *
XKBOARD_OBJFWD (lispfwd a)
{
  eassert (KBOARD_OBJFWDP (a));
  return a.fwdptr;
}
static struct Lisp_Intfwd const *
XFIXNUMFWD (lispfwd a)
{
  eassert (INTFWDP (a));
  return a.fwdptr;
}
static struct Lisp_Objfwd const *
XOBJFWD (lispfwd a)
{
  eassert (OBJFWDP (a));
  return a.fwdptr;
}

static void
set_blv_found (struct Lisp_Buffer_Local_Value *blv, int found)
{
  eassert (found == !BASE_EQ (blv->defcell, blv->valcell));
  blv->found = found;
}

static Lisp_Object
blv_value (struct Lisp_Buffer_Local_Value *blv)
{
  return XCDR (blv->valcell);
}

static void
set_blv_value (struct Lisp_Buffer_Local_Value *blv, Lisp_Object val)
{
  XSETCDR (blv->valcell, val);
}

static void
set_blv_where (struct Lisp_Buffer_Local_Value *blv, Lisp_Object val)
{
  blv->where = val;
}

static void
set_blv_defcell (struct Lisp_Buffer_Local_Value *blv, Lisp_Object val)
{
  blv->defcell = val;
}

static void
set_blv_valcell (struct Lisp_Buffer_Local_Value *blv, Lisp_Object val)
{
  blv->valcell = val;
}

static AVOID
wrong_length_argument (Lisp_Object a1, Lisp_Object a2, Lisp_Object a3)
{
  Lisp_Object size1 = make_fixnum (bool_vector_size (a1));
  Lisp_Object size2 = make_fixnum (bool_vector_size (a2));
  if (NILP (a3))
    xsignal2 (Qwrong_length_argument, size1, size2);
  else
    xsignal3 (Qwrong_length_argument, size1, size2,
	      make_fixnum (bool_vector_size (a3)));
}

AVOID
wrong_type_argument (Lisp_Object predicate, Lisp_Object value)
{
  //eassert (!TAGGEDP (value, Lisp_Type_Unused0));
  xsignal2 (Qwrong_type_argument, predicate, value);
}

void
args_out_of_range (Lisp_Object a1, Lisp_Object a2)
{
  xsignal2 (Qargs_out_of_range, a1, a2);
}

void
args_out_of_range_3 (Lisp_Object a1, Lisp_Object a2, Lisp_Object a3)
{
  xsignal3 (Qargs_out_of_range, a1, a2, a3);
}

void
circular_list (Lisp_Object list)
{
  xsignal1 (Qcircular_list, list);
}


/* Data type predicates.  */

/* MIGRATED TO GUILE: eq
   This function has been moved to prelude/load.scm as elisp-eq. */
DEFUN ("eq", Feq, Seq, 2, 2, 0,
       doc: /* Return t if the two args are the same Lisp object.  */
       attributes: const)
  (Lisp_Object obj1, Lisp_Object obj2)
{
  if (EQ (obj1, obj2))
    return Qt;
  return Qnil;
}


DEFUN ("type-of", Ftype_of, Stype_of, 1, 1, 0,
       doc: /* Return a symbol representing the type of OBJECT.
The symbol returned names the object's basic type;
for example, (type-of 1) returns `integer'.
Contrary to `cl-type-of', the returned type is not always the most
precise type possible, because instead this function tries to preserve
compatibility with the return value of previous Emacs versions.  */)
  (Lisp_Object object)
{
  return SYMBOLP (object)    ? Qsymbol
         : INTEGERP (object) ? Qinteger
         : Fcl_type_of (object);
}

DEFUN ("cl-type-of", Fcl_type_of, Scl_type_of, 1, 1, 0,
       doc: /* Return a symbol representing the type of OBJECT.
The returned symbol names the most specific possible type of the object.
for example, (cl-type-of nil) returns `null'.
The specific type returned may change depending on Emacs versions,
so we recommend you use `cl-typep', `cl-typecase', or other predicates
rather than compare the return value of this function against
a fixed set of types.  */)
  (Lisp_Object object)
{
  if (INTEGERP (object))
    return Qinteger;
  else if (SYMBOLP (object))
    return Qsymbol;
  else if (STRINGP (object))
    return Qstring;
  else if (CONSP (object))
    return Qcons;
  else if (GUILEBIGNUMP (object))
    return Qbignum;
  else if (GVECTORP (object))
    return Qvector;
  else if (VECTORLIKEP (object))
    {
      switch (PSEUDOVECTOR_TYPE (XVECTOR (object)))
        {
        case PVEC_NORMAL_VECTOR: return Qvector;
	case PVEC_MARKER: return Qmarker;
	case PVEC_OVERLAY: return Qoverlay;
	case PVEC_FINALIZER: return Qfinalizer;
	case PVEC_USER_PTR: return Quser_ptr;
        case PVEC_WINDOW_CONFIGURATION: return Qwindow_configuration;
        case PVEC_PROCESS: return Qprocess;
        case PVEC_WINDOW: return Qwindow;
        case PVEC_CLOSURE:
          return CONSP (AREF (object, CLOSURE_CODE))
                 ? Qinterpreted_function : Qbyte_code_function;
        case PVEC_BUFFER: return Qbuffer;
        case PVEC_CHAR_TABLE: return Qchar_table;
        case PVEC_BOOL_VECTOR: return Qbool_vector;
        case PVEC_FRAME: return Qframe;
        case PVEC_HASH_TABLE: return Qhash_table;
        case PVEC_OBARRAY: return Qobarray;
        case PVEC_FONT:
          if (FONT_SPEC_P (object))
	    return Qfont_spec;
          if (FONT_ENTITY_P (object))
	    return Qfont_entity;
          if (FONT_OBJECT_P (object))
	    return Qfont_object;
          else
            emacs_abort (); /* return Qfont?  */
        case PVEC_THREAD: return Qthread;
        case PVEC_MUTEX: return Qmutex;
        case PVEC_CONDVAR: return Qcondition_variable;
        case PVEC_TERMINAL: return Qterminal;
        case PVEC_RECORD:
          {
            Lisp_Object t = AREF (object, 0);
            if (RECORDP (t) && 1 < PVSIZE (t))
              /* Return the type name field of the class!  */
              return AREF (t, 1);
            else
              return t;
          }
        case PVEC_MODULE_FUNCTION:
          return Qmodule_function;
	case PVEC_NATIVE_COMP_UNIT:
          return Qnative_comp_unit;
        case PVEC_XWIDGET:
          return Qxwidget;
        case PVEC_XWIDGET_VIEW:
          return Qxwidget_view;
	case PVEC_TS_PARSER:
	  return Qtreesit_parser;
	case PVEC_TS_NODE:
	  return Qtreesit_node;
	case PVEC_TS_COMPILED_QUERY:
	  return Qtreesit_compiled_query;
        case PVEC_SQLITE:
          return Qsqlite;
        case PVEC_SUB_CHAR_TABLE:
          return Qsub_char_table;
        /* "Impossible" cases.  */
	case PVEC_MISC_PTR:
        case PVEC_OTHER:
        case PVEC_FREE: ;
        default:
          return Qvector;
        }
      emacs_abort ();
    }
  else if (FLOATP (object))
    return Qfloat;
  else if (! NILP (Fsubrp (object)))
    return Qsubr;
  else
    return Qt;
}

SLOWWRAP1(Flistp, "listp")

/* MIGRATED TO GUILE: nlistp
   This function has been moved to prelude/load.scm as elisp-nlistp. */
DEFUN ("nlistp", Fnlistp, Snlistp, 1, 1, 0,
       doc: /* Return t if OBJECT is not a list.  Lists include nil.  */
       attributes: const)
  (Lisp_Object object)
{
  if (CONSP (object) || NILP (object))
    return Qnil;
  return Qt;
}

/* MIGRATED TO GUILE: symbolp
   This function has been moved to prelude/load.scm as elisp-symbolp.
   Uses Guile's native symbol? predicate. */
DEFUN ("symbolp", Fsymbolp, Ssymbolp, 1, 1, 0,
       doc: /* Return t if OBJECT is a symbol.  */
       attributes: const)
  (Lisp_Object object)
{
  if (SYMBOLP (object))
    return Qt;
  return Qnil;
}

bool
SYMBOL_INTERNED_IN_INITIAL_OBARRAY_P (Lisp_Object sym)
{
  /* Should be initial_obarray */
  Lisp_Object tem = Ffind_symbol (SYMBOL_NAME (sym), Vobarray);
  return (! NILP (scm_c_value_ref (tem, 1))
          && (EQ (sym, scm_c_value_ref (tem, 0))));
}

/* MIGRATED TO GUILE: keywordp
   This function has been moved to prelude/load.scm as elisp-keywordp. */
DEFUN ("keywordp", Fkeywordp, Skeywordp, 1, 1, 0,
       doc: /* Return t if OBJECT is a keyword.
This means that it is a symbol with a print name beginning with `:'
interned in the initial obarray.  */)
  (Lisp_Object object)
{
  if (SYMBOLP (object)
      && guile_string_starts_with_char (SYMBOL_NAME (object), ':')
      && SYMBOL_INTERNED_IN_INITIAL_OBARRAY_P (object))
    return Qt;
  return Qnil;
}

/* MIGRATED TO GUILE: vectorp
   This function has been moved to prelude/load.scm as elisp-vectorp.
   Uses Guile's native vector? predicate. */
DEFUN ("vectorp", Fvectorp, Svectorp, 1, 1, 0,
       doc: /* Return t if OBJECT is a vector.  */)
  (Lisp_Object object)
{
  if (VECTOR_OR_PSEUDOVECTORP (object))
    return Qt;
  return Qnil;
}

/* MIGRATED TO GUILE: recordp
   This function has been moved to prelude/load.scm as elisp-recordp. */
DEFUN ("recordp", Frecordp, Srecordp, 1, 1, 0,
       doc: /* Return t if OBJECT is a record.  */)
  (Lisp_Object object)
{
  if (RECORDP (object))
    return Qt;
  return Qnil;
}

/* HOISTED TO SCHEME: stringp
   This function has been moved to prelude/load.scm as elisp-stringp.
   Zero C callers made it a perfect candidate for complete hoisting. */

/* HOISTED TO SCHEME: multibyte-string-p is now implemented in prelude/load.scm
   as elisp-multibyte-string-p. In Guilemacs all strings are UTF-8, so it
   always returns nil. */

/* MIGRATED TO GUILE: char-table-p
   This function has been moved to prelude/load.scm as elisp-char-table-p. */
DEFUN ("char-table-p", Fchar_table_p, Schar_table_p, 1, 1, 0,
       doc: /* Return t if OBJECT is a char-table.  */)
  (Lisp_Object object)
{
  if (CHAR_TABLE_P (object))
    return Qt;
  return Qnil;
}

/* MIGRATED TO GUILE: vector-or-char-table-p
   This function has been moved to prelude/load.scm as elisp-vector-or-char-table-p. */
DEFUN ("vector-or-char-table-p", Fvector_or_char_table_p,
       Svector_or_char_table_p, 1, 1, 0,
       doc: /* Return t if OBJECT is a char-table or vector.  */)
  (Lisp_Object object)
{
  if (VECTOR_OR_PSEUDOVECTORP (object) || CHAR_TABLE_P (object))
    return Qt;
  return Qnil;
}

/* MIGRATED TO GUILE: bool-vector-p
   This function has been moved to prelude/load.scm as elisp-bool-vector-p. */
DEFUN ("bool-vector-p", Fbool_vector_p, Sbool_vector_p, 1, 1, 0,
       doc: /* Return t if OBJECT is a bool-vector.  */)
  (Lisp_Object object)
{
  if (BOOL_VECTOR_P (object))
    return Qt;
  return Qnil;
}

/* MIGRATED TO GUILE: arrayp
   This function has been moved to prelude/load.scm as elisp-arrayp. */
DEFUN ("arrayp", Farrayp, Sarrayp, 1, 1, 0,
       doc: /* Return t if OBJECT is an array (string or vector).  */)
  (Lisp_Object object)
{
  if (ARRAYP (object))
    return Qt;
  return Qnil;
}

/* MIGRATED TO GUILE: sequencep
   This function has been moved to prelude/load.scm as elisp-sequencep.
   Uses Guile's native predicates for pairs, vectors, and strings. */
DEFUN ("sequencep", Fsequencep, Ssequencep, 1, 1, 0,
       doc: /* Return t if OBJECT is a sequence (list or array).  */)
  (register Lisp_Object object)
{
  if (CONSP (object) || NILP (object) || ARRAYP (object))
    return Qt;
  return Qnil;
}

DEFUN ("bufferp", Fbufferp, Sbufferp, 1, 1, 0,
       doc: /* Return t if OBJECT is an editor buffer.  */)
  (Lisp_Object object)
{
  if (BUFFERP (object))
    return Qt;
  return Qnil;
}

DEFUN ("markerp", Fmarkerp, Smarkerp, 1, 1, 0,
       doc: /* Return t if OBJECT is a marker (editor pointer).  */)
  (Lisp_Object object)
{
  if (MARKERP (object))
    return Qt;
  return Qnil;
}

#ifdef HAVE_MODULES
/* MIGRATED TO GUILE: user-ptrp
   This function has been moved to prelude/load.scm as elisp-user-ptrp.
   But we keep the C implementation for bootstrap. */
DEFUN ("user-ptrp", Fuser_ptrp, Suser_ptrp, 1, 1, 0,
       doc: /* Return t if OBJECT is a module user pointer.  */)
     (Lisp_Object object)
{
  if (USER_PTRP (object))
    return Qt;
  return Qnil;
}
#endif

/* MIGRATED TO GUILE: subrp
   This function has been moved to prelude/load.scm as elisp-subrp. */
DEFUN ("subrp", Fsubrp, Ssubrp, 1, 1, 0,
       doc: /* Return t if OBJECT is a built-in or native compiled Lisp function.

See also `primitive-function-p' and `native-comp-function-p'.  */)
  (Lisp_Object object)
{
  if (CONSP (object) && EQ (XCAR (object), Qspecial_operator))
    return Qt;
  if (SCM_PRIMITIVE_P (object))
    return Qt;
  return Qnil;
}

DEFUN ("closurep", Fclosurep, Sclosurep,
       1, 1, 0,
       doc: /* Return t if OBJECT is a function of type `closure'.  */)
  (Lisp_Object object)
{
  if (CLOSUREP (object))
    return Qt;
  return Qnil;
}

DEFUN ("byte-code-function-p", Fbyte_code_function_p, Sbyte_code_function_p,
       1, 1, 0,
       doc: /* Return t if OBJECT is a byte-compiled function object.  */)
  (Lisp_Object object)
{
  if (CLOSUREP (object) && STRINGP (AREF (object, CLOSURE_CODE)))
    return Qt;
  return Qnil;
}

DEFUN ("interpreted-function-p", Finterpreted_function_p,
       Sinterpreted_function_p, 1, 1, 0,
       doc: /* Return t if OBJECT is a function of type `interpreted-function'.  */)
  (Lisp_Object object)
{
  if (CLOSUREP (object) && CONSP (AREF (object, CLOSURE_CODE)))
    return Qt;
  return Qnil;
}

DEFUN ("module-function-p", Fmodule_function_p, Smodule_function_p, 1, 1, NULL,
       doc: /* Return t if OBJECT is a function loaded from a dynamic module.  */
       attributes: const)
  (Lisp_Object object)
{
  return MODULE_FUNCTIONP (object) ? Qt : Qnil;
}

DEFUN ("integer-or-marker-p", Finteger_or_marker_p, Sinteger_or_marker_p, 1, 1, 0,
       doc: /* Return t if OBJECT is an integer or a marker (editor pointer).  */)
  (register Lisp_Object object)
{
  if (MARKERP (object) || INTEGERP (object))
    return Qt;
  return Qnil;
}

DEFUN ("number-or-marker-p", Fnumber_or_marker_p,
       Snumber_or_marker_p, 1, 1, 0,
       doc: /* Return t if OBJECT is a number or a marker.  */)
  (Lisp_Object object)
{
  if (NUMBERP (object) || MARKERP (object))
    return Qt;
  return Qnil;
}

Lisp_Object
Fnatnump (Lisp_Object object)
{
  return call1 (intern ("natnump"), object);
}

Lisp_Object
Fcar (Lisp_Object list)
{
  return GUILECALL1(car, list);
}

/* MIGRATED TO GUILE: car-safe
   This function has been moved to prelude/load.scm as elisp-car-safe. */
DEFUN ("car-safe", Fcar_safe, Scar_safe, 1, 1, 0,
       doc: /* Return the car of OBJECT if it is a cons cell, or else nil.  */)
  (Lisp_Object object)
{
  return CAR_SAFE (object);
}

Lisp_Object
Fcdr (Lisp_Object list)
{
  return GUILECALL1(cdr, list);
}

/* MIGRATED TO GUILE: cdr-safe
   This function has been moved to prelude/load.scm as elisp-cdr-safe. */
DEFUN ("cdr-safe", Fcdr_safe, Scdr_safe, 1, 1, 0,
       doc: /* Return the cdr of OBJECT if it is a cons cell, or else nil.  */)
  (Lisp_Object object)
{
  return CDR_SAFE (object);
}

DEFUN ("setcar", Fsetcar, Ssetcar, 2, 2, 0,
       doc: /* Set the car of CELL to be NEWCAR.  Returns NEWCAR.  */)
  (register Lisp_Object cell, Lisp_Object newcar)
{
  CHECK_CONS (cell);
  CHECK_IMPURE (cell, XCONS (cell));
  XSETCAR (cell, newcar);
  return newcar;
}

DEFUN ("setcdr", Fsetcdr, Ssetcdr, 2, 2, 0,
       doc: /* Set the cdr of CELL to be NEWCDR.  Returns NEWCDR.  */)
  (register Lisp_Object cell, Lisp_Object newcdr)
{
  CHECK_CONS (cell);
  CHECK_IMPURE (cell, XCONS (cell));
  XSETCDR (cell, newcdr);
  return newcdr;
}

/* Extract and set components of symbols.  */

DEFUN ("boundp", Fboundp, Sboundp, 1, 1, 0,
       doc: /* Return t if SYMBOL's value is not void.
Note that if `lexical-binding' is in effect, this refers to the
global value outside of any lexical scope.  */)
  (register Lisp_Object symbol)
{
  Lisp_Object valcontents;
  sym_t sym;
  CHECK_SYMBOL (symbol);
  sym = XSYMBOL (symbol);

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_PLAINVAL: valcontents = SYMBOL_VAL (sym); break;
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_LOCALIZED:
      {
	struct Lisp_Buffer_Local_Value *blv = SYMBOL_BLV (sym);
	if (blv->fwd.fwdptr)
	  /* In set_internal, we un-forward vars when their value is
	     set to Qunbound.  */
    	  return Qt;
	else
	  {
	    swap_in_symval_forwarding (sym, blv);
	    valcontents = blv_value (blv);
	  }
	break;
      }
    case SYMBOL_FORWARDED:
      /* In set_internal, we un-forward vars when their value is
	 set to Qunbound.  */
      return Qt;
    default: emacs_abort ();
    }

  return (BASE_EQ (valcontents, Qunbound) ? Qnil : Qt);
}

WRAP1 (Fsymbol_function, "symbol-function")
/* It has been previously suggested to make this function an alias for
   symbol-function, but upon discussion at Bug#23957, there is a risk
   breaking backward compatibility, as some users of fboundp may
   expect t in particular, rather than any true value.  */
WRAP1 (Ffboundp, "fboundp")
WRAP1 (Fmakunbound, "makunbound")
WRAP1 (Ffmakunbound, "fmakunbound")
// FIX: guilemacs, if symbol is NILP, then do xsignal1 (Qsetting_constant, symbol)
WRAP2 (Ffset, "fset")

DEFUN ("symbol-plist", Fsymbol_plist, Ssymbol_plist, 1, 1, 0,
       doc: /* Return SYMBOL's property list.  */)
  (Lisp_Object symbol)
{
  CHECK_SYMBOL (symbol);
  return symbol_plist (symbol);
}

DEFUN ("symbol-name", Fsymbol_name, Ssymbol_name, 1, 1, 0,
       doc: /* Return SYMBOL's name, a string.

Warning: never alter the string returned by `symbol-name'.
Doing that might make Emacs dysfunctional, and might even crash Emacs.  */)
  (register Lisp_Object symbol)
{
  register Lisp_Object name;

  CHECK_SYMBOL (symbol);
  name = SYMBOL_NAME (symbol);
  return name;
}

DEFUN ("bare-symbol", Fbare_symbol, Sbare_symbol, 1, 1, 0,
       doc: /* Extract, if need be, the bare symbol from SYM.
SYM is either a symbol or a symbol with position.
Ignore `symbols-with-pos-enabled'.  */)
  (register Lisp_Object sym)
{
  return sym;
}

DEFUN ("symbol-with-pos-pos", Fsymbol_with_pos_pos, Ssymbol_with_pos_pos, 1, 1, 0,
       doc: /* Extract the position from the symbol with position SYMPOS.
Ignore `symbols-with-pos-enabled'.  */)
  (register Lisp_Object sympos)
{
  return Qnil;
}

DEFUN ("remove-pos-from-symbol", Fremove_pos_from_symbol,
       Sremove_pos_from_symbol, 1, 1, 0,
       doc: /* If ARG is a symbol with position, return it without the position.
Otherwise, return ARG unchanged.  Ignore `symbols-with-pos-enabled'.
Compare with `bare-symbol'.  */)
  (register Lisp_Object arg)
{
  return arg;
}

DEFUN ("position-symbol", Fposition_symbol, Sposition_symbol, 2, 2, 0,
       doc: /* Make a new symbol with position.
SYM is a symbol, with or without position, the symbol to position.
POS, the position, is either a nonnegative fixnum,
or a symbol with position from which the position will be taken.
Ignore `symbols-with-pos-enabled'.  */)
     (register Lisp_Object sym, register Lisp_Object pos)
{
  return sym;
}

static void
add_to_function_history (Lisp_Object symbol, Lisp_Object olddef)
{
  eassert (!NILP (olddef));

  Lisp_Object past = Fget (symbol, Qfunction_history);
  Lisp_Object file = Qnil;
  /* FIXME: Sadly, `Vload_file_name` gives less precise information
     (it's sometimes non-nil when it should be nil).  */
  Lisp_Object tail = Vcurrent_load_list;
  FOR_EACH_TAIL_SAFE (tail)
    if (NILP (XCDR (tail)) && STRINGP (XCAR (tail)))
      file = XCAR (tail);

  Lisp_Object tem = plist_member (past, file);
  if (!NILP (tem))
    { /* New def from a file used before.
         Overwrite the previous record associated with this file.  */
      if (EQ (tem, past))
        /* The new def is from the same file as the last change, so
           there's nothing to do: unloading the file should revert to
           the status before the last change rather than before this load.  */
        return;
      Lisp_Object pastlen = Flength (past);
      Lisp_Object temlen = Flength (tem);
      EMACS_INT tempos = XFIXNUM (pastlen) - XFIXNUM (temlen);
      eassert (tempos > 1);
      Lisp_Object prev = Fnthcdr (make_fixnum (tempos - 2), past);
      /* Remove the previous info for this file.
         E.g. change `hist` from (... OTHERFILE DEF3 THISFILE DEF2 ...)
         to (... OTHERFILE DEF2). */
      XSETCDR (prev, XCDR (tem));
    }
  /* Push new def from new file.  */
  Fput (symbol, Qfunction_history, Fcons (file, Fcons (olddef, past)));
}

void
defalias (Lisp_Object symbol, Lisp_Object definition)
{
  {
    bool autoload = AUTOLOADP (definition);
    if (!autoload)
      { /* Only add autoload entries after dumping, because the ones before are
	   not useful and else we get loads of them from the loaddefs.el.
	   That saves us about 110KB in the pdmp file (Jan 2022).  */
	LOADHIST_ATTACH (Fcons (Qdefun, symbol));
      }
  }

  {
    Lisp_Object olddef = SYMBOL_FUNCTION (symbol);
    if (!NILP (olddef))
      {
        if (!NILP (Vautoload_queue))
          Vautoload_queue = Fcons (symbol, Vautoload_queue);
        add_to_function_history (symbol, olddef);
      }
  }

  { /* Handle automatic advice activation.  */
    Lisp_Object hook = Fget (symbol, Qdefalias_fset_function);
    if (!NILP (hook))
      call2 (hook, symbol, definition);
    else
      Ffset (symbol, definition);
  }
}

DEFUN ("defalias", Fdefalias, Sdefalias, 2, 3, 0,
       doc: /* Set SYMBOL's function definition to DEFINITION.
Associates the function with the current load file, if any.
The optional third argument DOCSTRING specifies the documentation string
for SYMBOL; if it is omitted or nil, SYMBOL uses the documentation string
determined by DEFINITION.

Internally, this normally uses `fset', but if SYMBOL has a
`defalias-fset-function' property, the associated value is used instead.

The return value is undefined.  */)
  (register Lisp_Object symbol, Lisp_Object definition, Lisp_Object docstring)
{
  CHECK_SYMBOL (symbol);
  if (!NILP (Vpurify_flag)
      /* If `definition' is a keymap, immutable (and copying) is wrong.  */
      && !KEYMAPP (definition))
    definition = Fpurecopy (definition);

  defalias (symbol, definition);

  if (!NILP (docstring))
    Fput (symbol, Qfunction_documentation, docstring);
  /* We used to return `definition', but now that `defun' and `defmacro' expand
     to a call to `defalias', we return `symbol' for backward compatibility
     (bug#11686).  */
  return symbol;
}

DEFUN ("setplist", Fsetplist, Ssetplist, 2, 2, 0,
       doc: /* Set SYMBOL's property list to NEWPLIST, and return NEWPLIST.  */)
  (register Lisp_Object symbol, Lisp_Object newplist)
{
  CHECK_SYMBOL (symbol);
  set_symbol_plist (symbol, newplist);
  return newplist;
}

DEFUN ("subr-arity", Fsubr_arity, Ssubr_arity, 1, 1, 0,
       doc: /* Return minimum and maximum number of args allowed for SUBR.
SUBR must be a built-in function.
The returned value is a pair (MIN . MAX).  MIN is the minimum number
of args.  MAX is the maximum number or the symbol `many', for a
function with `&rest' args, or `unevalled' for a special form.  */)
  (Lisp_Object subr)
{
  Lisp_Object min, max;
  Lisp_Object arity;
  bool special = false;

  CHECK_SUBR (subr);
  if (CONSP (subr) && EQ (XCAR (subr), Qspecial_operator))
    {
      subr = XCDR (subr);
      special = true;
    }
  arity = scm_procedure_minimum_arity (subr);
  if (scm_is_false (arity))
    return Qnil;
  min = XCAR (arity);
  if (special)
    max = Qunevalled;
  else if (scm_is_true (XCAR (XCDR (XCDR (arity)))))
    max = Qmany;
  else
    max = scm_sum (min, XCAR (XCDR (arity)));
  return Fcons (min, max);
}

DEFUN ("subr-name", Fsubr_name, Ssubr_name, 1, 1, 0,
       doc: /* Return name of subroutine SUBR.
SUBR must be a built-in function.  */)
  (Lisp_Object subr)
{
  CHECK_SUBR (subr);
  if (CONSP (subr) && EQ (XCAR (subr), Qspecial_operator))
    subr = XCDR (subr);
  return Fsymbol_name (SCM_SUBR_NAME (subr));
}

DEFUN ("native-comp-function-p", Fnative_comp_function_p, Snative_comp_function_p, 1, 1,
       0, doc: /* Return t if the object is native compiled Lisp function, nil otherwise.  */)
  (Lisp_Object object)
{
  return NATIVE_COMP_FUNCTIONP (object) ? Qt : Qnil;
}

DEFUN ("subr-native-lambda-list", Fsubr_native_lambda_list,
       Ssubr_native_lambda_list, 1, 1, 0,
       doc: /* Return the lambda list for a native compiled lisp/d
function or t otherwise.  */)
  (Lisp_Object subr)
{
  CHECK_SUBR (subr);

  return Qt;
}

DEFUN ("subr-type", Fsubr_type,
       Ssubr_type, 1, 1, 0,
       doc: /* Return the type of SUBR.  */)
  (Lisp_Object subr)
{
  CHECK_SUBR (subr);
#ifdef HAVE_NATIVE_COMP
  return SUBR_TYPE (subr);
#else
  return Qnil;
#endif
}

#ifdef HAVE_NATIVE_COMP

DEFUN ("subr-native-comp-unit", Fsubr_native_comp_unit,
       Ssubr_native_comp_unit, 1, 1, 0,
       doc: /* Return the native compilation unit.  */)
  (Lisp_Object subr)
{
  CHECK_SUBR (subr);
  return XSUBR (subr)->native_comp_u;
}

DEFUN ("native-comp-unit-file", Fnative_comp_unit_file,
       Snative_comp_unit_file, 1, 1, 0,
       doc: /* Return the file of the native compilation unit.  */)
  (Lisp_Object comp_unit)
{
  CHECK_TYPE (NATIVE_COMP_UNITP (comp_unit), Qnative_comp_unit, comp_unit);
  return XNATIVE_COMP_UNIT (comp_unit)->file;
}

DEFUN ("native-comp-unit-set-file", Fnative_comp_unit_set_file,
       Snative_comp_unit_set_file, 2, 2, 0,
       doc: /* Return the file of the native compilation unit.  */)
  (Lisp_Object comp_unit, Lisp_Object new_file)
{
  CHECK_TYPE (NATIVE_COMP_UNITP (comp_unit), Qnative_comp_unit, comp_unit);
  XNATIVE_COMP_UNIT (comp_unit)->file = new_file;
  return comp_unit;
}

#endif

DEFUN ("interactive-form", Finteractive_form, Sinteractive_form, 1, 1, 0,
       doc: /* Return the interactive form of CMD or nil if none.
If CMD is not a command, the return value is nil.
Value, if non-nil, is a list (interactive SPEC).  */)
  (Lisp_Object cmd)
{
  Lisp_Object fun = indirect_function (cmd);
  bool genfun = false;

  if (NILP (fun))
    return Qnil;

  /* Use an `interactive-form' property if present, analogous to the
     function-documentation property.  */
  fun = cmd;
  while (SYMBOLP (fun))
    {
      Lisp_Object tmp = Fget (fun, Qinteractive_form);
      if (!NILP (tmp))
	return tmp;
      else
	fun = Fsymbol_function (fun);
    }

  if (CLOSUREP (fun))
    {
      if ((ASIZE (fun) & PSEUDOVECTOR_SIZE_MASK) > CLOSURE_INTERACTIVE)
	return list2 (Qinteractive, AREF (fun, CLOSURE_INTERACTIVE));
    }
  else if (scm_is_true (scm_procedure_p (fun)))
    {
      Lisp_Object tem = scm_assq (Qinteractive_form,
                                  scm_procedure_properties (fun));
      if (scm_is_pair (tem))
        return list2 (Qinteractive, scm_cdr (tem));
    }
#ifdef HAVE_MODULES
  else if (MODULE_FUNCTIONP (fun))
    {
      Lisp_Object form
        = module_function_interactive_form (XMODULE_FUNCTION (fun));
      if (! NILP (form))
        return form;
    }
#endif
  else if (AUTOLOADP (fun))
    return Finteractive_form (Fautoload_do_load (fun, cmd, Qnil));
  else if (CONSP (fun))
    {
      Lisp_Object funcar = XCAR (fun);
      if (EQ (funcar, Qlambda))
	{
	  Lisp_Object form = Fcdr (XCDR (fun));
	  Lisp_Object spec = Fassq (Qinteractive, form);
	  if (NILP (Fcdr (Fcdr (spec))))
	    return spec;
	  else
	    return list2 (Qinteractive, Fcar (Fcdr (spec)));
	}
    }
  if (genfun
      /* Avoid burping during bootstrap.  */
      && !NILP (Fsymbol_function (Qoclosure_interactive_form)))
    return call1 (Qoclosure_interactive_form, fun);
  else
    return Qnil;
}

DEFUN ("command-modes", Fcommand_modes, Scommand_modes, 1, 1, 0,
       doc: /* Return the modes COMMAND is defined for.
If COMMAND is not a command, the return value is nil.
The value, if non-nil, is a list of mode name symbols.  */)
  (Lisp_Object command)
{
  Lisp_Object fun = indirect_function (command);

  if (NILP (fun))
    return Qnil;

  /* Use a `command-modes' property if present, analogous to the
     function-documentation property.  */
  fun = command;
  while (SYMBOLP (fun))
    {
      Lisp_Object modes = Fget (fun, Qcommand_modes);
      if (!NILP (modes))
	return modes;
      else
	fun = Fsymbol_function (fun);
    }

  if (scm_is_true (scm_procedure_p (fun)))
    {
      return Qnil;
    }
  else if (CLOSUREP (fun))
    {
      if (PVSIZE (fun) <= CLOSURE_INTERACTIVE)
	return Qnil;
      Lisp_Object form = AREF (fun, CLOSURE_INTERACTIVE);
      if (VECTOR_OR_PSEUDOVECTORP (form))
	/* New form -- the second element is the command modes. */
	return AREF (form, 1);
      else
	/* Old .elc file -- no command modes. */
	return Qnil;
    }
#ifdef HAVE_MODULES
  else if (MODULE_FUNCTIONP (fun))
    {
      Lisp_Object form
        = module_function_command_modes (XMODULE_FUNCTION (fun));
      if (! NILP (form))
        return form;
    }
#endif
  else if (AUTOLOADP (fun))
    {
      Lisp_Object modes = Fnth (make_int (3), fun);
      if (CONSP (modes))
	return modes;
      else
	return Qnil;
    }
  else if (CONSP (fun))
    {
      Lisp_Object funcar = XCAR (fun);
      if (EQ (funcar, Qlambda))
	{
	  Lisp_Object form = Fcdr (XCDR (fun));
	  return Fcdr (Fcdr (Fassq (Qinteractive, form)));
	}
    }
  return Qnil;
}


/***********************************************************************
		Getting and Setting Values of Symbols
 ***********************************************************************/

DEFUN ("indirect-variable", Findirect_variable, Sindirect_variable, 1, 1, 0,
       doc: /* Return the variable at the end of OBJECT's variable chain.
If OBJECT is a symbol, follow its variable indirections (if any), and
return the variable at the end of the chain of aliases.  See Info node
`(elisp)Variable Aliases'.

If OBJECT is not a symbol, just return it.  */)
  (Lisp_Object object)
{
  if (SYMBOLP (object))
    {
      sym_t sym = XSYMBOL (object);
      while (SYMBOL_REDIRECT(sym) == SYMBOL_VARALIAS)
	sym = SYMBOL_ALIAS (sym);
      XSETSYMBOL (object, sym);
    }
  return object;
}

/* Return the KBOARD to which bindings currently established and values
   set should apply.  */

KBOARD *
kboard_for_bindings (void)
{
  /* We used to simply use current_kboard here, but from Lisp code, its
     value is often unexpected.  It seems nicer to allow constructions
     like this to work as intuitively expected:

     (with-selected-frame frame
     (define-key local-function-map "\eOP" [f1]))

     On the other hand, this affects the semantics of last-command and
     real-last-command, and people may rely on that.  I took a quick
     look at the Lisp codebase, and I don't think anything will break.
     --lorentey */

  return FRAME_KBOARD (SELECTED_FRAME ());
}

/* Given the raw contents of a symbol value cell,
   return the Lisp value of the symbol.
   This does not handle buffer-local variables; use
   swap_in_symval_forwarding for that.  */

Lisp_Object
do_symval_forwarding (lispfwd valcontents)
{
  switch (XFWDTYPE (valcontents))
    {
    case Lisp_Fwd_Int:
      return make_int (*XFIXNUMFWD (valcontents)->intvar);

    case Lisp_Fwd_Bool:
      return (*XBOOLFWD (valcontents)->boolvar ? Qt : Qnil);

    case Lisp_Fwd_Obj:
      return *XOBJFWD (valcontents)->objvar;

    case Lisp_Fwd_Buffer_Obj:
      return per_buffer_value (current_buffer,
			       XBUFFER_OBJFWD (valcontents)->offset);

    case Lisp_Fwd_Kboard_Obj:
      return *(Lisp_Object *) (XKBOARD_OBJFWD (valcontents)->offset
			       + (char *) kboard_for_bindings ());
    default: emacs_abort ();
    }
}

/* Used to signal a user-friendly error when symbol WRONG is
   not a member of CHOICE, which should be a list of symbols.  */

void
wrong_choice (Lisp_Object choice, Lisp_Object wrong)
{
  ptrdiff_t i = 0, len = list_length (choice);
  Lisp_Object obj, *args;
  AUTO_STRING (one_of, "One of ");
  AUTO_STRING (comma, ", ");
  AUTO_STRING (or, " or ");
  AUTO_STRING (should_be_specified, " should be specified");

  USE_SAFE_ALLOCA;
  SAFE_ALLOCA_LISP (args, len * 2 + 1);

  args[i++] = one_of;

  for (obj = choice; !NILP (obj); obj = XCDR (obj))
    {
      args[i++] = SYMBOL_NAME (XCAR (obj));
      args[i++] = (NILP (XCDR (obj)) ? should_be_specified
		   : NILP (XCDR (XCDR (obj))) ? or : comma);
    }

  obj = Fconcat (i, args);

  /* No need to call SAFE_FREE, since signaling does that for us.  */

  xsignal2 (Qerror, obj, wrong);
}

/* Used to signal a user-friendly error if WRONG is not a number or
   integer/floating-point number outsize of inclusive MIN..MAX range.  */

static void
wrong_range (Lisp_Object min, Lisp_Object max, Lisp_Object wrong)
{
  AUTO_STRING (value_should_be_from, "Value should be from ");
  AUTO_STRING (to, " to ");
  xsignal2 (Qerror,
	    CALLN (Fconcat, value_should_be_from, Fnumber_to_string (min),
		   to, Fnumber_to_string (max)),
	    wrong);
}

/* Store NEWVAL into SYMBOL, where VALCONTENTS is found in the value cell
   of SYMBOL.  If SYMBOL is buffer-local, VALCONTENTS should be the
   buffer-independent contents of the value cell: forwarded just one
   step past the buffer-localness.

   BUF non-zero means set the value in buffer BUF instead of the
   current buffer.  This only plays a role for per-buffer variables.  */

static void
store_symval_forwarding (lispfwd valcontents, Lisp_Object newval,
			 struct buffer *buf)
{
  switch (XFWDTYPE (valcontents))
    {
    case Lisp_Fwd_Int:
      {
	intmax_t i;
	CHECK_INTEGER (newval);
	if (! integer_to_intmax (newval, &i))
	  xsignal1 (Qoverflow_error, newval);
	*XFIXNUMFWD (valcontents)->intvar = i;
      }
      break;

    case Lisp_Fwd_Bool:
      *XBOOLFWD (valcontents)->boolvar = !NILP (newval);
      break;

    case Lisp_Fwd_Obj:
      *XOBJFWD (valcontents)->objvar = newval;

      /* If this variable is a default for something stored
	 in the buffer itself, such as default-fill-column,
	 find the buffers that don't have local values for it
	 and update them.  */
      if (XOBJFWD (valcontents)->objvar > (Lisp_Object *) &buffer_defaults
	  && XOBJFWD (valcontents)->objvar < (Lisp_Object *) (&buffer_defaults + 1))
	{
	  int offset = ((char *) XOBJFWD (valcontents)->objvar
			- (char *) &buffer_defaults);
	  int idx = PER_BUFFER_IDX (offset);

	  Lisp_Object tail, buf;

	  if (idx <= 0)
	    break;

	  FOR_EACH_LIVE_BUFFER (tail, buf)
	    {
	      struct buffer *b = XBUFFER (buf);

	      if (! PER_BUFFER_VALUE_P (b, idx))
		set_per_buffer_value (b, offset, newval);
	    }
	}
      break;

    case Lisp_Fwd_Buffer_Obj:
      {
	int offset = XBUFFER_OBJFWD (valcontents)->offset;
	Lisp_Object predicate = XBUFFER_OBJFWD (valcontents)->predicate;

	if (!NILP (newval) && !NILP (predicate))
	  {
	    eassert (SYMBOLP (predicate));
	    Lisp_Object choiceprop = Fget (predicate, Qchoice);
	    if (!NILP (choiceprop))
	      {
		if (NILP (Fmemq (newval, choiceprop)))
		  wrong_choice (choiceprop, newval);
	      }
	    else
	      {
		Lisp_Object rangeprop = Fget (predicate, Qrange);
		if (CONSP (rangeprop))
		  {
		    Lisp_Object min = XCAR (rangeprop), max = XCDR (rangeprop);
		    if (! NUMBERP (newval)
			|| (scm_leq_p (min, newval) == SCM_BOOL_F)
                        || (scm_leq_p (newval, max) == SCM_BOOL_F))
		      wrong_range (min, max, newval);
		  }
		else if (FUNCTIONP (predicate))
		  {
		    if (NILP (call1 (predicate, newval)))
		      wrong_type_argument (predicate, newval);
		  }
	      }
	  }
	if (buf == NULL)
	  buf = current_buffer;
	set_per_buffer_value (buf, offset, newval);
      }
      break;

    case Lisp_Fwd_Kboard_Obj:
      {
	char *base = (char *) kboard_for_bindings ();
	char *p = base + XKBOARD_OBJFWD (valcontents)->offset;
	*(Lisp_Object *) p = newval;
      }
      break;

    default:
      emacs_abort (); /* goto def; */
    }
}

/* Set up SYMBOL to refer to its global binding.  This makes it safe
   to alter the status of other bindings.  BEWARE: this may be called
   during the mark phase of GC, where we assume that Lisp_Object slots
   of BLV are marked after this function has changed them.  */

void
swap_in_global_binding (sym_t symbol)
{
  struct Lisp_Buffer_Local_Value *blv = SYMBOL_BLV (symbol);

  /* Unload the previously loaded binding.  */
  if (blv->fwd.fwdptr)
    set_blv_value (blv, do_symval_forwarding (blv->fwd));

  /* Select the global binding in the symbol.  */
  set_blv_valcell (blv, blv->defcell);
  if (blv->fwd.fwdptr)
    store_symval_forwarding (blv->fwd, XCDR (blv->defcell), NULL);

  /* Indicate that the global binding is set up now.  */
  set_blv_where (blv, Qnil);
  set_blv_found (blv, false);
}

/* Set up the buffer-local symbol SYMBOL for validity in the current buffer.
   VALCONTENTS is the contents of its value cell,
   which points to a struct Lisp_Buffer_Local_Value.

   Return the value forwarded one step past the buffer-local stage.
   This could be another forwarding pointer.  */

static void
swap_in_symval_forwarding (sym_t symbol, struct Lisp_Buffer_Local_Value *blv)
{
  register Lisp_Object tem1;

  eassert (blv == SYMBOL_BLV (symbol));

  tem1 = blv->where;

  if (NILP (tem1)
      || current_buffer != XBUFFER (tem1))
    {

      /* Unload the previously loaded binding.  */
      tem1 = blv->valcell;
      if (blv->fwd.fwdptr)
	set_blv_value (blv, do_symval_forwarding (blv->fwd));
      /* Choose the new binding.  */
      {
	Lisp_Object var;
	XSETSYMBOL (var, symbol);
	tem1 = assq_no_quit (var, BVAR (current_buffer, local_var_alist));
	set_blv_where (blv, Fcurrent_buffer ());
      }
      if (!(blv->found = !NILP (tem1)))
	tem1 = blv->defcell;

      /* Load the new binding.  */
      set_blv_valcell (blv, tem1);
      if (blv->fwd.fwdptr)
	store_symval_forwarding (blv->fwd, blv_value (blv), NULL);
    }
}

/* Find the value of a symbol, returning Qunbound if it's not bound.
   This is helpful for code which just wants to get a variable's value
   if it has one, without signaling an error.

   This function is very similar to buffer_local_value, but we have
   two separate code paths here since find_symbol_value has to be very
   efficient, while buffer_local_value doesn't have to be.

   Note that it must not be possible to quit within this function.
   Great care is required for this.  */

Lisp_Object
find_symbol_value (Lisp_Object symbol)
{
  sym_t sym;

  CHECK_SYMBOL (symbol);
  sym = XSYMBOL (symbol);

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_PLAINVAL: return SYMBOL_VAL (sym);
    case SYMBOL_LOCALIZED:
      {
	struct Lisp_Buffer_Local_Value *blv = SYMBOL_BLV (sym);
	swap_in_symval_forwarding (sym, blv);
	return (blv->fwd.fwdptr
		? do_symval_forwarding (blv->fwd)
		: blv_value (blv));
      }
    case SYMBOL_FORWARDED:
      return do_symval_forwarding (SYMBOL_FWD (sym));
    default: emacs_abort ();
    }
}

DEFUN ("symbol-value", Fsymbol_value, Ssymbol_value, 1, 1, 0,
       doc: /* Return SYMBOL's value.  Error if that is void.
Note that if `lexical-binding' is in effect, this returns the
global value outside of any lexical scope.  */)
  (Lisp_Object symbol)
{
  Lisp_Object val;

  val = find_symbol_value (symbol);
  if (!BASE_EQ (val, Qunbound))
    return val;

  xsignal1 (Qvoid_variable, symbol);
}

DEFUN ("set", Fset, Sset, 2, 2, 0,
       doc: /* Set SYMBOL's value to NEWVAL, and return NEWVAL.  */)
  (register Lisp_Object symbol, Lisp_Object newval)
{
  set_internal (symbol, newval, Qnil, SET_INTERNAL_SET);
  return newval;
}

/* Store the value NEWVAL into SYMBOL.
   If buffer-locality is an issue, WHERE specifies which context to use.
   (nil stands for the current buffer/frame).

   If BINDFLAG is SET_INTERNAL_SET, then if this symbol is supposed to
   become local in every buffer where it is set, then we make it
   local.  If BINDFLAG is SET_INTERNAL_BIND or SET_INTERNAL_UNBIND, we
   don't do that.  */

void
set_internal (Lisp_Object symbol, Lisp_Object newval, Lisp_Object where,
              enum Set_Internal_Bind bindflag)
{
  bool unbinding_p = BASE_EQ (newval, Qunbound);

  /* If restoring in a dead buffer, do nothing.  */

  CHECK_SYMBOL (symbol);
  sym_t sym = XSYMBOL (symbol);
  switch (SYMBOL_TRAPPED (sym))
    {
    case SYMBOL_NOWRITE:
      if (NILP (Fkeywordp (symbol))
          || !EQ (newval, Fsymbol_value (symbol)))
        xsignal1 (Qsetting_constant, symbol);
      else
        /* Allow setting keywords to their own value.  */
        return;

    case SYMBOL_TRAPPED_WRITE:
      /* Setting due to thread-switching doesn't count.  */
      if (bindflag != SET_INTERNAL_THREAD_SWITCH)
        notify_variable_watchers (symbol, (unbinding_p ? Qnil : newval),
                                  (bindflag == SET_INTERNAL_BIND
				   ? Qlet
				   : (bindflag == SET_INTERNAL_UNBIND
				      ? Qunlet
				      : (unbinding_p
					 ? Qmakunbound : Qset))),
                                  where);
      break;

    case SYMBOL_UNTRAPPED_WRITE:
      break;

    default: emacs_abort ();
    }

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_PLAINVAL: SET_SYMBOL_VAL (sym , newval); return;
    case SYMBOL_LOCALIZED:
      {
	struct Lisp_Buffer_Local_Value *blv = SYMBOL_BLV (sym);

	if (unbinding_p && blv->fwd.fwdptr)
	  /* Forbid unbinding built-in variables.  */
	  error ("Built-in variables may not be unbound");

	if (NILP (where))
	  XSETBUFFER (where, current_buffer);

	/* If the current buffer is not the buffer whose binding is
	   loaded, or if it's a Lisp_Buffer_Local_Value and
	   the default binding is loaded, the loaded binding may be the
	   wrong one.  */
	if (!BASE_EQ (blv->where, where)
	    /* Also unload a global binding (if the var is local_if_set).  */
	    || (BASE_EQ (blv->valcell, blv->defcell)))
	  {
	    /* The currently loaded binding is not necessarily valid.
	       We need to unload it, and choose a new binding.  */

	    /* Write out `realvalue' to the old loaded binding.  */
	    if (blv->fwd.fwdptr)
	      set_blv_value (blv, do_symval_forwarding (blv->fwd));

	    /* Find the new binding.  */
	    XSETSYMBOL (symbol, sym); /* May have changed via aliasing.  */
	    Lisp_Object tem1
	      = assq_no_quit (symbol,
			      BVAR (XBUFFER (where), local_var_alist));
	    set_blv_where (blv, where);
	    blv->found = true;

	    if (NILP (tem1))
	      {
		/* This buffer still sees the default value.  */

		/* If the variable is a Lisp_Some_Buffer_Local_Value,
		   or if this is `let' rather than `set',
		   make CURRENT-ALIST-ELEMENT point to itself,
		   indicating that we're seeing the default value.
		   Likewise if the variable has been let-bound
		   in the current buffer.  */
		if (bindflag || !blv->local_if_set
		    || let_shadows_buffer_binding_p (sym))
		  {
		    blv->found = false;
		    tem1 = blv->defcell;
		  }
		/* If it's a local_if_set, being set not bound,
		   and we're not within a let that was made for this buffer,
		   create a new buffer-local binding for the variable.
		   That means, give this buffer a new assoc for a local value
		   and load that binding.  */
		else
		  {
		    tem1 = Fcons (symbol, XCDR (blv->defcell));
		    bset_local_var_alist
		      (XBUFFER (where),
		       Fcons (tem1, BVAR (XBUFFER (where), local_var_alist)));
		  }
	      }

	    /* Record which binding is now loaded.  */
	    set_blv_valcell (blv, tem1);
	  }

	/* Store the new value in the cons cell.  */
	set_blv_value (blv, newval);

	if (blv->fwd.fwdptr)
	  store_symval_forwarding (blv->fwd, newval, (BUFFERP (where)
						      ? XBUFFER (where)
						      : current_buffer));
	break;
      }
    case SYMBOL_FORWARDED:
      {
	struct buffer *buf
	  = BUFFERP (where) ? XBUFFER (where) : current_buffer;
	lispfwd innercontents = SYMBOL_FWD (sym);

	if (unbinding_p)
	  /* Forbid unbinding built-in variables.  */
	  error ("Built-in variables may not be unbound");

	if (BUFFER_OBJFWDP (innercontents))
	  {
	    int offset = XBUFFER_OBJFWD (innercontents)->offset;
	    int idx = PER_BUFFER_IDX (offset);
	    if (idx > 0 && bindflag == SET_INTERNAL_SET
	        && !PER_BUFFER_VALUE_P (buf, idx))
	      {
		if (let_shadows_buffer_binding_p (sym))
		  set_default_internal (symbol, newval, bindflag,
					NULL);
		else
		  SET_PER_BUFFER_VALUE_P (buf, idx, 1);
	      }
	  }

	store_symval_forwarding (/* sym, */ innercontents, newval, buf);
	break;
      }
    default: emacs_abort ();
    }
  return;
}

static void
set_symbol_trapped_write (Lisp_Object symbol, enum symbol_trapped_write trap)
{
  sym_t sym = XSYMBOL (symbol);
  if (SYMBOL_TRAPPED (sym) == SYMBOL_NOWRITE)
    xsignal1 (Qtrapping_constant, symbol);
  SET_SYMBOL_TRAPPED (sym, trap);
}

static void
restore_symbol_trapped_write (Lisp_Object symbol)
{
  set_symbol_trapped_write (symbol, SYMBOL_TRAPPED_WRITE);
}

static void
harmonize_variable_watchers (Lisp_Object alias, Lisp_Object base_variable)
{
  if (!EQ (base_variable, alias)
      && EQ (base_variable, Findirect_variable (alias)))
    set_symbol_trapped_write
      (alias, SYMBOL_TRAPPED(XSYMBOL (base_variable)));
}

DEFUN ("add-variable-watcher", Fadd_variable_watcher, Sadd_variable_watcher,
       2, 2, 0,
       doc: /* Cause WATCH-FUNCTION to be called when SYMBOL is about to be set.

It will be called with 4 arguments: (SYMBOL NEWVAL OPERATION WHERE).
SYMBOL is the variable being changed.
NEWVAL is the value it will be changed to.  (The variable still has
the old value when WATCH-FUNCTION is called.)
OPERATION is a symbol representing the kind of change, one of: `set',
`let', `unlet', `makunbound', and `defvaralias'.
WHERE is a buffer if the buffer-local value of the variable is being
changed, nil otherwise.

All writes to aliases of SYMBOL will call WATCH-FUNCTION too.  */)
  (Lisp_Object symbol, Lisp_Object watch_function)
{
  symbol = Findirect_variable (symbol);
  CHECK_SYMBOL (symbol);
  set_symbol_trapped_write (symbol, SYMBOL_TRAPPED_WRITE);
  map_obarray (Vobarray, harmonize_variable_watchers, symbol);

  Lisp_Object watchers = Fget (symbol, Qwatchers);
  Lisp_Object member = Fmember (watch_function, watchers);
  if (NILP (member))
    Fput (symbol, Qwatchers, Fcons (watch_function, watchers));
  return Qnil;
}

DEFUN ("remove-variable-watcher", Fremove_variable_watcher, Sremove_variable_watcher,
       2, 2, 0,
       doc: /* Undo the effect of `add-variable-watcher'.
Remove WATCH-FUNCTION from the list of functions to be called when
SYMBOL (or its aliases) are set.  */)
  (Lisp_Object symbol, Lisp_Object watch_function)
{
  symbol = Findirect_variable (symbol);
  Lisp_Object watchers = Fget (symbol, Qwatchers);
  watchers = Fdelete (watch_function, watchers);
  if (NILP (watchers))
    {
      set_symbol_trapped_write (symbol, SYMBOL_UNTRAPPED_WRITE);
      map_obarray (Vobarray, harmonize_variable_watchers, symbol);
    }
  Fput (symbol, Qwatchers, watchers);
  return Qnil;
}

DEFUN ("get-variable-watchers", Fget_variable_watchers, Sget_variable_watchers,
       1, 1, 0,
       doc: /* Return a list of SYMBOL's active watchers.  */)
  (Lisp_Object symbol)
{
  return (SYMBOL_TRAPPED_WRITE_P (symbol) == SYMBOL_TRAPPED_WRITE)
    ? Fget (Findirect_variable (symbol), Qwatchers)
    : Qnil;
}

void
notify_variable_watchers (Lisp_Object symbol,
                          Lisp_Object newval,
                          Lisp_Object operation,
                          Lisp_Object where)
{
  symbol = Findirect_variable (symbol);

  dynwind_begin ();
  record_unwind_protect (restore_symbol_trapped_write, symbol);
  /* Avoid recursion.  */
  set_symbol_trapped_write (symbol, SYMBOL_UNTRAPPED_WRITE);

  if (NILP (where)
      && !EQ (operation, Qset_default) && !EQ (operation, Qmakunbound)
      && !NILP (Flocal_variable_if_set_p (symbol, Fcurrent_buffer ())))
    {
      XSETBUFFER (where, current_buffer);
    }

  if (EQ (operation, Qset_default))
    operation = Qset;

  for (Lisp_Object watchers = Fget (symbol, Qwatchers);
       CONSP (watchers);
       watchers = XCDR (watchers))
    {
      Lisp_Object watcher = XCAR (watchers);
#if 0 // guilemacs, no SUBRP
      /* Call subr directly to avoid gc.  */
      if (SUBRP (watcher))
        {
          Lisp_Object args[] = { symbol, newval, operation, where };
          funcall_subr (XSUBR (watcher), ARRAYELTS (args), args);
        }
      else
        calln (watcher, symbol, newval, operation, where);
#endif
    }

  dynwind_end ();
}


/* Access or set a buffer-local symbol's default value.  */

/* Return the default value of SYMBOL, but don't check for voidness.
   Return Qunbound if it is void.  */

Lisp_Object
default_value (Lisp_Object symbol)
{
  sym_t sym;

  CHECK_SYMBOL (symbol);
  sym = XSYMBOL (symbol);

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_PLAINVAL: return SYMBOL_VAL (sym);
    case SYMBOL_LOCALIZED:
      {
	/* If var is set up for a buffer that lacks a local value for it,
	   the current value is nominally the default value.
	   But the `realvalue' slot may be more up to date, since
	   ordinary setq stores just that slot.  So use that.  */
	struct Lisp_Buffer_Local_Value *blv = SYMBOL_BLV (sym);
	if (blv->fwd.fwdptr && BASE_EQ (blv->valcell, blv->defcell))
	  return do_symval_forwarding (blv->fwd);
	else
	  return XCDR (blv->defcell);
      }
    case SYMBOL_FORWARDED:
      {
	lispfwd valcontents = SYMBOL_FWD (sym);

	/* For a built-in buffer-local variable, get the default value
	   rather than letting do_symval_forwarding get the current value.  */
	if (BUFFER_OBJFWDP (valcontents))
	  {
	    int offset = XBUFFER_OBJFWD (valcontents)->offset;
	    if (PER_BUFFER_IDX (offset) != 0)
	      return per_buffer_default (offset);
	  }

	/* For other variables, get the current value.  */
	return do_symval_forwarding (valcontents);
      }
    default: emacs_abort ();
    }
}

DEFUN ("default-boundp", Fdefault_boundp, Sdefault_boundp, 1, 1, 0,
       doc: /* Return t if SYMBOL has a non-void default value.
A variable may have a buffer-local value.  This function says whether
the variable has a non-void value outside of the current buffer
context.  Also see `default-value'.  */)
  (Lisp_Object symbol)
{
  register Lisp_Object value;

  value = default_value (symbol);
  return (BASE_EQ (value, Qunbound) ? Qnil : Qt);
}

DEFUN ("default-value", Fdefault_value, Sdefault_value, 1, 1, 0,
       doc: /* Return SYMBOL's default value.
This is the value that is seen in buffers that do not have their own values
for this variable.  The default value is meaningful for variables with
local bindings in certain buffers.  */)
  (Lisp_Object symbol)
{
  Lisp_Object value = default_value (symbol);
  if (!BASE_EQ (value, Qunbound))
    return value;

  xsignal1 (Qvoid_variable, symbol);
}

void
set_default_internal (Lisp_Object symbol, Lisp_Object value,
                      enum Set_Internal_Bind bindflag, KBOARD *where)
{
  CHECK_SYMBOL (symbol);
  sym_t sym = XSYMBOL (symbol);
  switch (SYMBOL_TRAPPED (sym))
    {
    case SYMBOL_NOWRITE:
      if (NILP (Fkeywordp (symbol))
          || !EQ (value, Fsymbol_value (symbol)))
        xsignal1 (Qsetting_constant, symbol);
      else
        /* Allow setting keywords to their own value.  */
        return;

    case SYMBOL_TRAPPED_WRITE:
      /* Don't notify here if we're going to call Fset anyway.  */
      if (SYMBOL_REDIRECT (sym) != SYMBOL_PLAINVAL
          /* Setting due to thread switching doesn't count.  */
          && bindflag != SET_INTERNAL_THREAD_SWITCH)
        notify_variable_watchers (symbol, value, Qset_default, Qnil);
      break;

    case SYMBOL_UNTRAPPED_WRITE:
      break;

    default: emacs_abort ();
    }

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_PLAINVAL: set_internal (symbol, value, Qnil, bindflag); return;
    case SYMBOL_LOCALIZED:
      {
	struct Lisp_Buffer_Local_Value *blv = SYMBOL_BLV (sym);

	/* Store new value into the DEFAULT-VALUE slot.  */
	XSETCDR (blv->defcell, value);

	/* If the default binding is now loaded, set the REALVALUE slot too.  */
	if (blv->fwd.fwdptr && BASE_EQ (blv->defcell, blv->valcell))
	  store_symval_forwarding (blv->fwd, value, NULL);
        return;
      }
    case SYMBOL_FORWARDED:
      {
	lispfwd valcontents = SYMBOL_FWD (sym);

	/* Handle variables like case-fold-search that have special slots
	   in the buffer.
	   Make them work apparently like Lisp_Buffer_Local_Value variables.  */
	if (BUFFER_OBJFWDP (valcontents))
	  {
	    int offset = XBUFFER_OBJFWD (valcontents)->offset;
	    int idx = PER_BUFFER_IDX (offset);

	    set_per_buffer_default (offset, value);

	    /* If this variable is not always local in all buffers,
	       set it in the buffers that don't nominally have a local value.  */
	    if (idx > 0)
	      {
		Lisp_Object buf, tail;

		/* Do this only in live buffers, so that if there are
		   a lot of buffers which are dead, that doesn't slow
		   down let-binding of variables that are
		   automatically local when set, like
		   case-fold-search.  This is for Lisp programs that
		   let-bind such variables in their inner loops.  */
		FOR_EACH_LIVE_BUFFER (tail, buf)
		  {
		    struct buffer *b = XBUFFER (buf);

		    if (!PER_BUFFER_VALUE_P (b, idx))
		      set_per_buffer_value (b, offset, value);
		  }
	      }
	  }
	else if (KBOARD_OBJFWDP (valcontents))
	  {
	    char *base = (char *) (where ? where
				   : kboard_for_bindings ());
	    char *p = base + XKBOARD_OBJFWD (valcontents)->offset;
	    *(Lisp_Object *) p = value;
	  }
	else
          set_internal (symbol, value, Qnil, bindflag);
        return;
      }
    default: emacs_abort ();
    }
}

// FIX: 20190626 LAV, this should probably be removed (similar to what happened with "setq-default")
DEFUN ("set-default", Fset_default, Sset_default, 2, 2, 0,
       doc: /* Set SYMBOL's default value to VALUE.  SYMBOL and VALUE are evaluated.
The default value is seen in buffers that do not have their own values
for this variable.  */)
  (Lisp_Object symbol, Lisp_Object value)
{
  set_default_internal (symbol, value, SET_INTERNAL_SET, NULL);
  return value;
}


/* Lisp functions for creating and removing buffer-local variables.  */

union Lisp_Val_Fwd
  {
    Lisp_Object value;
    lispfwd fwd;
  };

static struct Lisp_Buffer_Local_Value *
make_blv (sym_t sym, bool forwarded,
	  union Lisp_Val_Fwd valcontents)
{
  struct Lisp_Buffer_Local_Value *blv = xmalloc (sizeof *blv);
  Lisp_Object symbol;
  Lisp_Object tem;

 XSETSYMBOL (symbol, sym);
 tem = Fcons (symbol, (forwarded
                       ? do_symval_forwarding (valcontents.fwd)
                       : valcontents.value));

  /* Buffer_Local_Values cannot have as realval a buffer-local
     or keyboard-local forwarding.  */
  eassert (!(forwarded && BUFFER_OBJFWDP (valcontents.fwd)));
  eassert (!(forwarded && KBOARD_OBJFWDP (valcontents.fwd)));
  if (forwarded)
    blv->fwd = valcontents.fwd;
  else
    blv->fwd.fwdptr = NULL;
  set_blv_where (blv, Qnil);
  blv->local_if_set = 0;
  set_blv_defcell (blv, tem);
  set_blv_valcell (blv, tem);
  set_blv_found (blv, false);
  __lsan_ignore_object (blv);
  return blv;
}

DEFUN ("make-variable-buffer-local", Fmake_variable_buffer_local,
       Smake_variable_buffer_local, 1, 1, "vMake Variable Buffer Local: ",
       doc: /* Make VARIABLE become buffer-local whenever it is set.
At any time, the value for the current buffer is in effect,
unless the variable has never been set in this buffer,
in which case the default value is in effect.
Note that binding the variable with `let', or setting it while
a `let'-style binding made in this buffer is in effect,
does not make the variable buffer-local.  Return VARIABLE.

This globally affects all uses of this variable, so it belongs together with
the variable declaration, rather than with its uses (if you just want to make
a variable local to the current buffer for one particular use, use
`make-local-variable').  Buffer-local bindings are normally cleared
while setting up a new major mode, unless they have a `permanent-local'
property.

The function `default-value' gets the default value and `set-default' sets it.

See also `defvar-local'.  */)
  (register Lisp_Object variable)
{
  sym_t sym;
  struct Lisp_Buffer_Local_Value *blv = NULL;
  union Lisp_Val_Fwd valcontents UNINIT;
  bool forwarded UNINIT;

  CHECK_SYMBOL (variable);
  sym = XSYMBOL (variable);

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_PLAINVAL:
      forwarded = 0; valcontents.value = SYMBOL_VAL (sym);
      if (BASE_EQ (valcontents.value, Qunbound))
	valcontents.value = Qnil;
      break;
    case SYMBOL_LOCALIZED:
      blv = SYMBOL_BLV (sym);
      break;
    case SYMBOL_FORWARDED:
      forwarded = 1; valcontents.fwd = SYMBOL_FWD (sym);
      if (KBOARD_OBJFWDP (valcontents.fwd))
	error ("Symbol %s may not be buffer-local",
	       SDATA (SYMBOL_NAME (variable)));
      else if (BUFFER_OBJFWDP (valcontents.fwd))
	return variable;
      break;
    default: emacs_abort ();
    }

  if (SYMBOL_CONSTANT_P (variable))
    xsignal1 (Qsetting_constant, variable);

  if (!blv)
    {
      blv = make_blv (sym, forwarded, valcontents);
      SET_SYMBOL_REDIRECT (sym, SYMBOL_LOCALIZED);
      SET_SYMBOL_BLV (sym, blv);
    }

  blv->local_if_set = 1;
  return variable;
}

DEFUN ("make-local-variable", Fmake_local_variable, Smake_local_variable,
       1, 1, "vMake Local Variable: ",
       doc: /* Make VARIABLE have a separate value in the current buffer.
Other buffers will continue to share a common default value.
\(The buffer-local value of VARIABLE starts out as the same value
VARIABLE previously had.  If VARIABLE was void, it remains void.)
Return VARIABLE.

If the variable is already arranged to become local when set,
this function causes a local value to exist for this buffer,
just as setting the variable would do.

This function returns VARIABLE, and therefore
  (set (make-local-variable \\='VARIABLE) VALUE-EXP)
works.

See also `make-variable-buffer-local'.

Do not use `make-local-variable' to make a hook variable buffer-local.
Instead, use `add-hook' and specify t for the LOCAL argument.  */)
  (Lisp_Object variable)
{
  Lisp_Object tem;
  bool forwarded UNINIT;
  union Lisp_Val_Fwd valcontents UNINIT;
  sym_t sym;
  struct Lisp_Buffer_Local_Value *blv = NULL;

  CHECK_SYMBOL (variable);
  sym = XSYMBOL (variable);

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_PLAINVAL:
      forwarded = 0; valcontents.value = SYMBOL_VAL (sym); break;
    case SYMBOL_LOCALIZED:
      blv = SYMBOL_BLV (sym);
      break;
    case SYMBOL_FORWARDED:
      forwarded = 1; valcontents.fwd = SYMBOL_FWD (sym);
      if (KBOARD_OBJFWDP (valcontents.fwd))
	error ("Symbol %s may not be buffer-local",
	       SDATA (SYMBOL_NAME (variable)));
      break;
    default: emacs_abort ();
    }

  if (SYMBOL_TRAPPED (sym) == SYMBOL_NOWRITE)
    xsignal1 (Qsetting_constant, variable);

  if (!blv)
    {
      if (forwarded && BUFFER_OBJFWDP (valcontents.fwd))
        {
          int offset = XBUFFER_OBJFWD (valcontents.fwd)->offset;
          int idx = PER_BUFFER_IDX (offset);
          eassert (idx);
          if (idx > 0)
            /* If idx < 0, it's always buffer local, like `mode-name`.  */
            SET_PER_BUFFER_VALUE_P (current_buffer, idx, true);
          return variable;
        }
      blv = make_blv (sym, forwarded, valcontents);
      SET_SYMBOL_REDIRECT (sym, SYMBOL_LOCALIZED);
      SET_SYMBOL_BLV (sym, blv);
    }

  /* Make sure this buffer has its own value of symbol.  */
  XSETSYMBOL (variable, sym);	/* Update in case of aliasing.  */
  tem = assq_no_quit (variable, BVAR (current_buffer, local_var_alist));
  if (NILP (tem))
    {
      if (let_shadows_buffer_binding_p (sym))
	{
	  AUTO_STRING (format,
		       "Making %s buffer-local while locally let-bound!");
	  CALLN (Fmessage, format, SYMBOL_NAME (variable));
	}

      if (BUFFERP (blv->where) && current_buffer == XBUFFER (blv->where))
        /* Make sure the current value is permanently recorded, if it's the
           default value.  */
        swap_in_global_binding (sym);

      bset_local_var_alist
	(current_buffer,
	 Fcons (Fcons (variable, XCDR (blv->defcell)),
		BVAR (current_buffer, local_var_alist)));

      /* If the symbol forwards into a C variable, then load the binding
         for this buffer now, to preserve the invariant that forwarded
         variables must always hold the value corresponding to the
         current buffer (they are swapped eagerly).
         Otherwise, if C code modifies the variable before we load the
         binding in, then that new value would clobber the default binding
         the next time we unload it.  See bug#34318.  */
      if (blv->fwd.fwdptr)
        swap_in_symval_forwarding (sym, blv);
    }

  return variable;
}

DEFUN ("kill-local-variable", Fkill_local_variable, Skill_local_variable,
       1, 1, "vKill Local Variable: ",
       doc: /* Make VARIABLE no longer have a separate value in the current buffer.
From now on the default value will apply in this buffer.  Return VARIABLE.  */)
  (register Lisp_Object variable)
{
  register Lisp_Object tem;
  struct Lisp_Buffer_Local_Value *blv;
  sym_t sym;

  CHECK_SYMBOL (variable);
  sym = XSYMBOL (variable);

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_PLAINVAL: return variable;
    case SYMBOL_FORWARDED:
      {
	lispfwd valcontents = SYMBOL_FWD (sym);
	if (BUFFER_OBJFWDP (valcontents))
	  {
	    int offset = XBUFFER_OBJFWD (valcontents)->offset;
	    int idx = PER_BUFFER_IDX (offset);

	    if (idx > 0)
	      {
		SET_PER_BUFFER_VALUE_P (current_buffer, idx, 0);
		set_per_buffer_value (current_buffer, offset,
				      per_buffer_default (offset));
	      }
	  }
	return variable;
      }
    case SYMBOL_LOCALIZED:
      blv = SYMBOL_BLV (sym);
      break;
    default: emacs_abort ();
    }

  if (SYMBOL_TRAPPED (sym) == SYMBOL_TRAPPED_WRITE)
    notify_variable_watchers (variable, Qnil, Qmakunbound, Fcurrent_buffer ());

  /* Get rid of this buffer's alist element, if any.  */
  XSETSYMBOL (variable, sym);	/* Propagate variable indirection.  */
  tem = assq_no_quit (variable, BVAR (current_buffer, local_var_alist));
  if (!NILP (tem))
    bset_local_var_alist
      (current_buffer,
       Fdelq (tem, BVAR (current_buffer, local_var_alist)));

  /* If the symbol is set up with the current buffer's binding
     loaded, recompute its value.  We have to do it now, or else
     forwarded objects won't work right.  */
  {
    Lisp_Object buf; XSETBUFFER (buf, current_buffer);
    if (BASE_EQ (buf, blv->where))
      swap_in_global_binding (sym);
  }

  return variable;
}

/* Lisp functions for creating and removing buffer-local variables.  */

DEFUN ("local-variable-p", Flocal_variable_p, Slocal_variable_p,
       1, 2, 0,
       doc: /* Non-nil if VARIABLE has a local binding in buffer BUFFER.
BUFFER defaults to the current buffer.

Also see `buffer-local-boundp'.*/)
  (Lisp_Object variable, Lisp_Object buffer)
{
  struct buffer *buf = decode_buffer (buffer);
  sym_t sym;

  CHECK_SYMBOL (variable);
  sym = XSYMBOL (variable);

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_PLAINVAL: return Qnil;
    case SYMBOL_LOCALIZED:
      {
	Lisp_Object tmp;
	struct Lisp_Buffer_Local_Value *blv = SYMBOL_BLV (sym);
	XSETBUFFER (tmp, buf);
	XSETSYMBOL (variable, sym); /* Update in case of aliasing.  */

	if (BASE_EQ (blv->where, tmp)) /* The binding is already loaded.  */
	  return blv_found (blv) ? Qt : Qnil;
	else
	  return NILP (assq_no_quit (variable, BVAR (buf, local_var_alist)))
	    ? Qnil
	    : Qt;
      }
    case SYMBOL_FORWARDED:
      {
	lispfwd valcontents = SYMBOL_FWD (sym);
	if (BUFFER_OBJFWDP (valcontents))
	  {
	    int offset = XBUFFER_OBJFWD (valcontents)->offset;
	    int idx = PER_BUFFER_IDX (offset);
	    if (idx == -1 || PER_BUFFER_VALUE_P (buf, idx))
	      return Qt;
	  }
	return Qnil;
      }
    default: emacs_abort ();
    }
}

DEFUN ("local-variable-if-set-p", Flocal_variable_if_set_p, Slocal_variable_if_set_p,
       1, 2, 0,
       doc: /* Non-nil if VARIABLE is local in buffer BUFFER when set there.
BUFFER defaults to the current buffer.

More precisely, return non-nil if either VARIABLE already has a local
value in BUFFER, or if VARIABLE is automatically buffer-local (see
`make-variable-buffer-local').  */)
  (register Lisp_Object variable, Lisp_Object buffer)
{
  sym_t sym;

  CHECK_SYMBOL (variable);
  sym = XSYMBOL (variable);

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_PLAINVAL: return Qnil;
    case SYMBOL_LOCALIZED:
      {
	struct Lisp_Buffer_Local_Value *blv = SYMBOL_BLV (sym);
	if (blv->local_if_set)
	  return Qt;
	XSETSYMBOL (variable, sym); /* Update in case of aliasing.  */
	return Flocal_variable_p (variable, buffer);
      }
    case SYMBOL_FORWARDED:
      /* All BUFFER_OBJFWD slots become local if they are set.  */
      return (BUFFER_OBJFWDP (SYMBOL_FWD (sym)) ? Qt : Qnil);
    default: emacs_abort ();
    }
}

DEFUN ("variable-binding-locus", Fvariable_binding_locus, Svariable_binding_locus,
       1, 1, 0,
       doc: /* Return a value indicating where VARIABLE's current binding comes from.
If the current binding is buffer-local, the value is the current buffer.
If the current binding is global (the default), the value is nil.  */)
  (register Lisp_Object variable)
{
  sym_t sym;

  CHECK_SYMBOL (variable);
  sym = XSYMBOL (variable);

  /* Make sure the current binding is actually swapped in.  */
  find_symbol_value (variable);

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS: sym = SYMBOL_ALIAS (sym); goto start;
    case SYMBOL_PLAINVAL: return Qnil;
    case SYMBOL_FORWARDED:
      {
	lispfwd valcontents = SYMBOL_FWD (sym);
	if (KBOARD_OBJFWDP (valcontents))
	  return Fframe_terminal (selected_frame);
	else if (!BUFFER_OBJFWDP (valcontents))
	  return Qnil;
      }
      FALLTHROUGH;
    case SYMBOL_LOCALIZED:
      /* For a local variable, record both the symbol and which
	 buffer's or frame's value we are saving.  */
      if (!NILP (Flocal_variable_p (variable, Qnil)))
	return Fcurrent_buffer ();
      else if (SYMBOL_REDIRECT (sym) == SYMBOL_LOCALIZED
	       && blv_found (SYMBOL_BLV (sym)))
	return SYMBOL_BLV (sym)->where;
      else
	return Qnil;
    default: emacs_abort ();
    }
}


/* Find the function at the end of a chain of symbol function indirections.  */

/* If OBJECT is a symbol, find the end of its function chain and
   return the value found there.  If OBJECT is not a symbol, just
   return it.  */
Lisp_Object
indirect_function (Lisp_Object object)
{
  while (SYMBOLP (object) && !NILP (object))
    object = SYMBOL_FUNCTION (object);
  return object;
}

DEFUN ("indirect-function", Findirect_function, Sindirect_function, 1, 2, 0,
       doc: /* Return the function at the end of OBJECT's function chain.
If OBJECT is not a symbol, just return it.  Otherwise, follow all
function indirections to find the final function binding and return it.  */)
  (Lisp_Object object, Lisp_Object noerror)
{
  return indirect_function (object);
}

/* Extract and set vector and string elements.  */

DEFUN ("aref", Faref, Saref, 2, 2, 0,
       doc: /* Return the element of ARRAY at index IDX.
ARRAY may be a vector, a string, a char-table, a bool-vector, a record,
or a byte-code object.  IDX starts at 0.  */)
  (register Lisp_Object array, Lisp_Object idx)
{
  register EMACS_INT idxval;

  CHECK_FIXNUM (idx);
  idxval = XFIXNUM (idx);
  if (STRINGP (array))
    {
      if (idxval < 0 || idxval >= SCHARS (array))
	args_out_of_range (array, idx);

      return make_fixnum (SREF (array, idxval));
    }
  else if (BOOL_VECTOR_P (array))
    {
      if (idxval < 0 || idxval >= bool_vector_size (array))
	args_out_of_range (array, idx);
      return bool_vector_ref (array, idxval);
    }
  else if (CHAR_TABLE_P (array))
    {
      CHECK_CHARACTER (idx);
      return CHAR_TABLE_REF (array, idxval);
    }
  else
    {
      ptrdiff_t size;
      if (CLOSUREP (array) || RECORDP (array))
	size = PVSIZE (array);
      else if (PLAIN_VECTORP (array))
	size = ASIZE (array);
      else
	wrong_type_argument (Qarrayp, array);

      if (idxval < 0 || idxval >= size)
	args_out_of_range (array, idx);

      return AREF (array, idxval);
    }
}

DEFUN ("aset", Faset, Saset, 3, 3, 0,
       doc: /* Store into the element of ARRAY at index IDX the value NEWELT.
Return NEWELT.  ARRAY may be a vector, a string, a char-table or a
bool-vector.  IDX starts at 0.  */)
  (register Lisp_Object array, Lisp_Object idx, Lisp_Object newelt)
{
  register EMACS_INT idxval;

  CHECK_FIXNUM (idx);
  idxval = XFIXNUM (idx);
  if (! RECORDP (array))
    CHECK_ARRAY (array, Qarrayp);

  if (RECORDP (array))
    {
      CHECK_IMPURE (array, XVECTOR (array));
      if (idxval < 0 || idxval >= PVSIZE (array))
	args_out_of_range (array, idx);
      ASET (array, idxval, newelt);
    }
  else if (PLAIN_VECTORP (array))
    {
      if (VECTORLIKEP (array))
	CHECK_IMPURE (array, XVECTOR (array));
      if (idxval < 0 || idxval >= ASIZE (array))
	args_out_of_range (array, idx);
      ASET (array, idxval, newelt);
    }
  else if (BOOL_VECTOR_P (array))
    {
      if (idxval < 0 || idxval >= bool_vector_size (array))
	args_out_of_range (array, idx);
      bool_vector_set (array, idxval, !NILP (newelt));
    }
  else if (CHAR_TABLE_P (array))
    {
      CHECK_CHARACTER (idx);
      CHAR_TABLE_SET (array, idxval, newelt);
    }
  else /* STRINGP */
    {
      CHECK_IMPURE (array, XSTRING (array));
      if (idxval < 0 || idxval >= SCHARS (array))
	args_out_of_range (array, idx);
      CHECK_CHARACTER (newelt);

      // Use Guile native string mutation
      scm_string_set_x (array, scm_from_size_t (idxval), scm_integer_to_char (newelt));
    }

  return newelt;
}

/* Arithmetic functions */

static Lisp_Object
check_integer_coerce_marker (Lisp_Object x)
{
  if (MARKERP (x))
    return make_fixnum (marker_position (x));
  CHECK_TYPE (INTEGERP (x), Qinteger_or_marker_p, x);
  return x;
}

Lisp_Object
check_number_coerce_marker (Lisp_Object x)
{
  if (MARKERP (x))
    return make_fixnum (marker_position (x));
  CHECK_TYPE (NUMBERP (x), Qnumber_or_marker_p, x);
  return x;
}

static Lisp_Object
coerce_marker (Lisp_Object x)
{
  return MARKERP (x) ? make_fixnum (marker_position (x)) : x;
}

static AVOID
not_number_or_marker (Lisp_Object x)
{
  wrong_type_argument (Qnumber_or_marker_p, x);
}

cmp_bits_t
arithcompare (Lisp_Object num1, Lisp_Object num2)
{
  num1 = coerce_marker (num1);
  num2 = coerce_marker (num2);

  bool lt, eq, gt;

  if ((FLOATP (num1) && scm_nan_p (num1) == SCM_BOOL_T) ||
      (FLOATP (num2) && scm_nan_p (num2) == SCM_BOOL_T))
    {
      eq = false;
      lt = false;
      gt = false;
    }
  else if ((INTEGERP (num1) || FLOATP (num1)) &&
           (INTEGERP (num2) || FLOATP (num2)))
    {
      int cmp = value_cmp_scm (num1, num2);
      eq = cmp == 0;
      lt = cmp < 0;
      gt = cmp > 0;
    }
  else
    {
      if (!(INTEGERP (num1) || FLOATP (num1)))
        {
          not_number_or_marker (num1);
        }
      not_number_or_marker (num2);
    }

  return lt << Cmp_Bit_LT | gt << Cmp_Bit_GT | eq << Cmp_Bit_EQ;
}


/* Convert the cons-of-integers, integer, or float value C to an
   unsigned value with maximum value MAX, where MAX is one less than a
   power of 2.  Signal an error if C does not have a valid format or
   is out of range.

   Although Emacs represents large integers with bignums instead of
   cons-of-integers or floats, for now this function still accepts the
   obsolete forms in case some old Lisp code still generates them.  */
uintmax_t
cons_to_unsigned (Lisp_Object c, uintmax_t max)
{
  bool valid = false;
  uintmax_t val UNINIT;

  if (FLOATP (c))
    {
      double d = XFLOAT_DATA (c);
      if (d >= 0 && d < 1.0 + max)
	{
	  val = d;
	  valid = val == d;
	}
    }
  else
    {
      Lisp_Object hi = CONSP (c) ? XCAR (c) : c;
      valid = INTEGERP (hi) && integer_to_uintmax (hi, &val);

      if (valid && CONSP (c))
	{
	  uintmax_t top = val;
	  Lisp_Object rest = XCDR (c);
	  if (top <= UINTMAX_MAX >> 24 >> 16
	      && CONSP (rest)
	      && FIXNATP (XCAR (rest)) && XFIXNAT (XCAR (rest)) < 1 << 24
	      && FIXNATP (XCDR (rest)) && XFIXNAT (XCDR (rest)) < 1 << 16)
	    {
	      uintmax_t mid = XFIXNAT (XCAR (rest));
	      val = top << 24 << 16 | mid << 16 | XFIXNAT (XCDR (rest));
	    }
	  else
	    {
	      valid = top <= UINTMAX_MAX >> 16;
	      if (valid)
		{
		  if (CONSP (rest))
		    rest = XCAR (rest);
		  valid = FIXNATP (rest) && XFIXNAT (rest) < 1 << 16;
		  if (valid)
		    val = top << 16 | XFIXNAT (rest);
		}
	    }
	}
    }

  if (! (valid && val <= max))
    error ("Not an in-range integer, integral float, or cons of integers");
  return val;
}

/* Convert the cons-of-integers, integer, or float value C to a signed
   value with extrema MIN and MAX.  MAX should be one less than a
   power of 2, and MIN should be zero or the negative of a power of 2.
   Signal an error if C does not have a valid format or is out of
   range.

   Although Emacs represents large integers with bignums instead of
   cons-of-integers or floats, for now this function still accepts the
   obsolete forms in case some old Lisp code still generates them.  */
intmax_t
cons_to_signed (Lisp_Object c, intmax_t min, intmax_t max)
{
  bool valid = false;
  intmax_t val UNINIT;

  if (FLOATP (c))
    {
      double d = XFLOAT_DATA (c);
      if (d >= min && d < 1.0 + max)
	{
	  val = d;
	  valid = val == d;
	}
    }
  else
    {
      Lisp_Object hi = CONSP (c) ? XCAR (c) : c;
      valid = INTEGERP (hi) && integer_to_intmax (hi, &val);

      if (valid && CONSP (c))
	{
	  intmax_t top = val;
	  Lisp_Object rest = XCDR (c);
	  if (top >= INTMAX_MIN >> 24 >> 16 && top <= INTMAX_MAX >> 24 >> 16
	      && CONSP (rest)
	      && FIXNATP (XCAR (rest)) && XFIXNAT (XCAR (rest)) < 1 << 24
	      && FIXNATP (XCDR (rest)) && XFIXNAT (XCDR (rest)) < 1 << 16)
	    {
	      intmax_t mid = XFIXNAT (XCAR (rest));
	      val = top << 24 << 16 | mid << 16 | XFIXNAT (XCDR (rest));
	    }
	  else
	    {
	      valid = INTMAX_MIN >> 16 <= top && top <= INTMAX_MAX >> 16;
	      if (valid)
		{
		  if (CONSP (rest))
		    rest = XCAR (rest);
		  valid = FIXNATP (rest) && XFIXNAT (rest) < 1 << 16;
		  if (valid)
		    val = top << 16 | XFIXNAT (rest);
		}
	    }
	}
    }

  if (! (valid && min <= val && val <= max))
    error ("Not an in-range integer, integral float, or cons of integers");
  return val;
}

/* Render NUMBER in decimal into BUFFER which ends right before END.
   Return the start of the string; the end is always at END.
   The string is not null-terminated.  */
char *
fixnum_to_string (EMACS_INT number, char *buffer, char *end)
{
  EMACS_INT x = number;
  bool negative = x < 0;
  if (negative)
    x = -x;
  char *p = end;
  do
    {
      eassume (p > buffer && p - 1 < end);
      *--p = '0' + x % 10;
      x /= 10;
    }
  while (x);
  if (negative)
    *--p = '-';
  return p;
}

DEFUN ("number-to-string", Fnumber_to_string, Snumber_to_string, 1, 1, 0,
       doc: /* Return the decimal representation of NUMBER as a string.
Uses a minus sign if negative.
NUMBER may be an integer or a floating point number.  */)
  (Lisp_Object number)
{
  char buffer[max (FLOAT_TO_STRING_BUFSIZE, INT_BUFSIZE_BOUND (EMACS_INT))];

  if (FIXNUMP (number))
    {
      char *end = buffer + sizeof buffer;
      char *p = fixnum_to_string (XFIXNUM (number), buffer, end);
      //return make_unibyte_string (p, end - p);
      return scm_from_utf8_stringn (p, end - p);
    }

  if (GUILEBIGNUMP (number))
    {
      // guilemacs, missing ancient feature: If BASE is negative, use upper-case digits in base -BASE.
      return scm_number_to_string (number, make_fixnum (10));
    }

  if (FLOATP (number))
    {
      /* Optimize: Use Guile's native float-to-string conversion */
      return scm_number_to_string (number, make_fixnum (10));
    }

  wrong_type_argument (Qnumberp, number);
}

DEFUN ("string-to-number", Fstring_to_number, Sstring_to_number, 1, 2, 0,
       doc: /* Parse STRING as a decimal number and return the number.
Ignore leading spaces and tabs, and all trailing chars.  Return 0 if
STRING cannot be parsed as an integer or floating point number.

If BASE, interpret STRING as a number in that base.  If BASE isn't
present, base 10 is used.  BASE must be between 2 and 16 (inclusive).
If the base used is not 10, STRING is always parsed as an integer.  */)
  (register Lisp_Object string, Lisp_Object base)
{
  int b;

  CHECK_STRING (string);

  if (NILP (base))
    b = 10;
  else
    {
      CHECK_FIXNUM (base);
      if (! (XFIXNUM (base) >= 2 && XFIXNUM (base) <= 16))
	xsignal1 (Qargs_out_of_range, base);
      b = XFIXNUM (base);
    }

  char *p = SSDATA (string);
  while (*p == ' ' || *p == '\t')
    p++;

  Lisp_Object val = string_to_number (p, b, 0);
  return ((IEEE_FLOATING_POINT ? NILP (val) : !NUMBERP (val))
	  ? make_fixnum (0) : val);
}
Lisp_Object
string_from_scheme (Lisp_Object scheme_string)
{
  emacs_abort ();
  size_t nbytes;
  char *c_string = scm_to_utf8_stringn (scheme_string, &nbytes);
  Lisp_Object result = make_string_from_bytes (c_string,
                                               scm_c_string_length (scheme_string),
                                               nbytes);
  free (c_string);
  return result;
}
Lisp_Object
string_to_scheme (Lisp_Object string)
{
  return string;  /* String is already a Guile string - no conversion needed */
}

/* Because we round up the bool vector allocate size to word_size
   units, we can safely read past the "end" of the vector in the
   operations below.  These extra bits are always zero.  */

static bits_word
bool_vector_spare_mask (EMACS_INT nr_bits)
{
  return (((bits_word) 1) << (nr_bits % BITS_PER_BITS_WORD)) - 1;
}

enum bool_vector_op { bool_vector_exclusive_or,
                      bool_vector_union,
                      bool_vector_intersection,
                      bool_vector_set_difference,
                      bool_vector_subsetp };

static Lisp_Object
bool_vector_binop_driver (Lisp_Object a,
                          Lisp_Object b,
                          Lisp_Object dest,
                          enum bool_vector_op op)
{
  EMACS_INT nr_bits;
  bits_word *adata, *bdata, *destdata;
  ptrdiff_t i = 0;
  ptrdiff_t nr_words;

  CHECK_BOOL_VECTOR (a);
  CHECK_BOOL_VECTOR (b);

  nr_bits = bool_vector_size (a);
  if (bool_vector_size (b) != nr_bits)
    wrong_length_argument (a, b, dest);

  nr_words = bool_vector_words (nr_bits);
  adata = bool_vector_data (a);
  bdata = bool_vector_data (b);

  if (NILP (dest))
    {
      dest = make_uninit_bool_vector (nr_bits);
      destdata = bool_vector_data (dest);
    }
  else
    {
      CHECK_BOOL_VECTOR (dest);
      destdata = bool_vector_data (dest);
      if (bool_vector_size (dest) != nr_bits)
	wrong_length_argument (a, b, dest);

      switch (op)
	{
	case bool_vector_exclusive_or:
	  for (; i < nr_words; i++)
	    if (destdata[i] != (adata[i] ^ bdata[i]))
	      goto set_dest;
	  break;

	case bool_vector_subsetp:
	  for (; i < nr_words; i++)
	    if (adata[i] &~ bdata[i])
	      return Qnil;
	  return Qt;

	case bool_vector_union:
	  for (; i < nr_words; i++)
	    if (destdata[i] != (adata[i] | bdata[i]))
	      goto set_dest;
	  break;

	case bool_vector_intersection:
	  for (; i < nr_words; i++)
	    if (destdata[i] != (adata[i] & bdata[i]))
	      goto set_dest;
	  break;

	case bool_vector_set_difference:
	  for (; i < nr_words; i++)
	    if (destdata[i] != (adata[i] &~ bdata[i]))
	      goto set_dest;
	  break;
	}

      return Qnil;
    }

 set_dest:
  switch (op)
    {
    case bool_vector_exclusive_or:
      for (; i < nr_words; i++)
	destdata[i] = adata[i] ^ bdata[i];
      break;

    case bool_vector_union:
      for (; i < nr_words; i++)
	destdata[i] = adata[i] | bdata[i];
      break;

    case bool_vector_intersection:
      for (; i < nr_words; i++)
	destdata[i] = adata[i] & bdata[i];
      break;

    case bool_vector_set_difference:
      for (; i < nr_words; i++)
	destdata[i] = adata[i] &~ bdata[i];
      break;

    default:
      eassume (0);
    }

  return dest;
}

DEFUN ("bool-vector-exclusive-or", Fbool_vector_exclusive_or,
       Sbool_vector_exclusive_or, 2, 3, 0,
       doc: /* Return A ^ B, bitwise exclusive or.
If optional third argument C is given, store result into C.
A, B, and C must be bool vectors of the same length.
Return the destination vector if it changed or nil otherwise.  */)
  (Lisp_Object a, Lisp_Object b, Lisp_Object c)
{
  return bool_vector_binop_driver (a, b, c, bool_vector_exclusive_or);
}

DEFUN ("bool-vector-union", Fbool_vector_union,
       Sbool_vector_union, 2, 3, 0,
       doc: /* Return A | B, bitwise or.
If optional third argument C is given, store result into C.
A, B, and C must be bool vectors of the same length.
Return the destination vector if it changed or nil otherwise.  */)
  (Lisp_Object a, Lisp_Object b, Lisp_Object c)
{
  return bool_vector_binop_driver (a, b, c, bool_vector_union);
}

DEFUN ("bool-vector-intersection", Fbool_vector_intersection,
       Sbool_vector_intersection, 2, 3, 0,
       doc: /* Return A & B, bitwise and.
If optional third argument C is given, store result into C.
A, B, and C must be bool vectors of the same length.
Return the destination vector if it changed or nil otherwise.  */)
  (Lisp_Object a, Lisp_Object b, Lisp_Object c)
{
  return bool_vector_binop_driver (a, b, c, bool_vector_intersection);
}

DEFUN ("bool-vector-set-difference", Fbool_vector_set_difference,
       Sbool_vector_set_difference, 2, 3, 0,
       doc: /* Return A &~ B, set difference.
If optional third argument C is given, store result into C.
A, B, and C must be bool vectors of the same length.
Return the destination vector if it changed or nil otherwise.  */)
  (Lisp_Object a, Lisp_Object b, Lisp_Object c)
{
  return bool_vector_binop_driver (a, b, c, bool_vector_set_difference);
}

DEFUN ("bool-vector-subsetp", Fbool_vector_subsetp,
       Sbool_vector_subsetp, 2, 2, 0,
       doc: /* Return t if every t value in A is also t in B, nil otherwise.
A and B must be bool vectors of the same length.  */)
  (Lisp_Object a, Lisp_Object b)
{
  return bool_vector_binop_driver (a, b, b, bool_vector_subsetp);
}

DEFUN ("bool-vector-not", Fbool_vector_not,
       Sbool_vector_not, 1, 2, 0,
       doc: /* Compute ~A, set complement.
If optional second argument B is given, store result into B.
A and B must be bool vectors of the same length.
Return the destination vector.  */)
  (Lisp_Object a, Lisp_Object b)
{
  EMACS_INT nr_bits;
  bits_word *bdata, *adata;
  ptrdiff_t i;

  CHECK_BOOL_VECTOR (a);
  nr_bits = bool_vector_size (a);

  if (NILP (b))
    b = make_uninit_bool_vector (nr_bits);
  else
    {
      CHECK_BOOL_VECTOR (b);
      if (bool_vector_size (b) != nr_bits)
	wrong_length_argument (a, b, Qnil);
    }

  bdata = bool_vector_data (b);
  adata = bool_vector_data (a);

  for (i = 0; i < nr_bits / BITS_PER_BITS_WORD; i++)
    bdata[i] = BITS_WORD_MAX & ~adata[i];

  if (nr_bits % BITS_PER_BITS_WORD)
    {
      bits_word mword = bits_word_to_host_endian (adata[i]);
      mword = ~mword;
      mword &= bool_vector_spare_mask (nr_bits);
      bdata[i] = bits_word_to_host_endian (mword);
    }

  return b;
}

DEFUN ("bool-vector-count-population", Fbool_vector_count_population,
       Sbool_vector_count_population, 1, 1, 0,
       doc: /* Count how many elements in A are t.
A is a bool vector.  To count A's nil elements, subtract the return
value from A's length.  */)
  (Lisp_Object a)
{
  EMACS_INT count;
  EMACS_INT nr_bits;
  bits_word *adata;
  ptrdiff_t i, nwords;

  CHECK_BOOL_VECTOR (a);

  nr_bits = bool_vector_size (a);
  nwords = bool_vector_words (nr_bits);
  count = 0;
  adata = bool_vector_data (a);

  for (i = 0; i < nwords; i++)
    count += stdc_count_ones (adata[i]);

  return make_fixnum (count);
}

DEFUN ("bool-vector-count-consecutive", Fbool_vector_count_consecutive,
       Sbool_vector_count_consecutive, 3, 3, 0,
       doc: /* Count how many consecutive elements in A equal B starting at I.
A is a bool vector, B is t or nil, and I is an index into A.  */)
  (Lisp_Object a, Lisp_Object b, Lisp_Object i)
{
  EMACS_INT count;
  EMACS_INT nr_bits;
  int offset;
  bits_word *adata;
  bits_word twiddle;
  bits_word mword; /* Machine word.  */
  ptrdiff_t pos, pos0;
  ptrdiff_t nr_words;

  CHECK_BOOL_VECTOR (a);
  CHECK_FIXNAT (i);

  nr_bits = bool_vector_size (a);
  if (XFIXNAT (i) > nr_bits) /* Allow one past the end for convenience */
    args_out_of_range (a, i);

  adata = bool_vector_data (a);
  nr_words = bool_vector_words (nr_bits);
  pos = XFIXNAT (i) / BITS_PER_BITS_WORD;
  offset = XFIXNAT (i) % BITS_PER_BITS_WORD;
  count = 0;

  /* By XORing with twiddle, we transform the problem of "count
     consecutive equal values" into "count the zero bits".  The latter
     operation usually has hardware support.  */
  twiddle = NILP (b) ? 0 : BITS_WORD_MAX;

  /* Scan the remainder of the mword at the current offset.  */
  if (pos < nr_words && offset != 0)
    {
      mword = bits_word_to_host_endian (adata[pos]);
      mword ^= twiddle;
      mword >>= offset;

      /* Do not count the pad bits.  */
      mword |= (bits_word) 1 << (BITS_PER_BITS_WORD - offset);

      count = stdc_trailing_zeros (mword);
      pos++;
      if (count + offset < BITS_PER_BITS_WORD)
        return make_fixnum (count);
    }

  /* Scan whole words until we either reach the end of the vector or
     find an mword that doesn't completely match.  twiddle is
     endian-independent.  */
  pos0 = pos;
  while (pos < nr_words && adata[pos] == twiddle)
    pos++;
  count += (pos - pos0) * BITS_PER_BITS_WORD;

  if (pos < nr_words)
    {
      /* If we stopped because of a mismatch, see how many bits match
         in the current mword.  */
      mword = bits_word_to_host_endian (adata[pos]);
      mword ^= twiddle;
      count += stdc_trailing_zeros (mword);
    }
  else if (nr_bits % BITS_PER_BITS_WORD != 0)
    {
      /* If we hit the end, we might have overshot our count.  Reduce
         the total by the number of spare bits at the end of the
         vector.  */
      count -= BITS_PER_BITS_WORD - nr_bits % BITS_PER_BITS_WORD;
    }

  return make_fixnum (count);
}


DEFUN ("bind-symbol", Fbind_symbol, Sbind_symbol, 3, 3, 0,
       doc: /* Bind symbol.  */)
  (Lisp_Object symbol, Lisp_Object value, Lisp_Object thunk)
{
  Lisp_Object val;
  dynwind_begin ();
  specbind (symbol, value);
  val = call0 (thunk);
  dynwind_end ();
  return val;
}


void
syms_of_data (void)
{
  Lisp_Object error_tail, arith_tail, recursion_tail;

  /* wrapper functions that uses the guile version */
  DEFSYM(Fsymbol_function_sym, "symbol-function");
  DEFSYM(Ffboundp_sym, "fboundp")
  DEFSYM(Fmakunbound_sym, "makunbound")
  DEFSYM(Ffmakunbound_sym, "fmakunbound")
  DEFSYM(Ffset_sym, "fset")

  /* Used by defsubr.  */
  DEFSYM (Qspecial_operator, "special-operator");
  DEFSYM (Qinteractive_form, "interactive-form");

#include "data.x"

  DEFSYM (Qquote, "quote");
  DEFSYM (Qlambda, "lambda");
  DEFSYM (Qerror_conditions, "error-conditions");
  DEFSYM (Qerror_message, "error-message");
  DEFSYM (Qtop_level, "top-level");

  DEFSYM (Qerror, "error");
  DEFSYM (Quser_error, "user-error");
  DEFSYM (Qquit, "quit");
  DEFSYM (Qminibuffer_quit, "minibuffer-quit");
  DEFSYM (Qwrong_length_argument, "wrong-length-argument");
  DEFSYM (Qwrong_type_argument, "wrong-type-argument");
  DEFSYM (Qtype_mismatch, "type-mismatch")
  DEFSYM (Qargs_out_of_range, "args-out-of-range");
  DEFSYM (Qvoid_function, "void-function");
  DEFSYM (Qcyclic_function_indirection, "cyclic-function-indirection");
  DEFSYM (Qcyclic_variable_indirection, "cyclic-variable-indirection");
  DEFSYM (Qvoid_variable, "void-variable");
  DEFSYM (Qsetting_constant, "setting-constant");
  DEFSYM (Qtrapping_constant, "trapping-constant");
  DEFSYM (Qinvalid_read_syntax, "invalid-read-syntax");

  DEFSYM (Qinvalid_function, "invalid-function");
  DEFSYM (Qwrong_number_of_arguments, "wrong-number-of-arguments");
  DEFSYM (Qno_catch, "no-catch");
  DEFSYM (Qend_of_file, "end-of-file");
  DEFSYM (Qarith_error, "arith-error");
  DEFSYM (Qbeginning_of_buffer, "beginning-of-buffer");
  DEFSYM (Qend_of_buffer, "end-of-buffer");
  DEFSYM (Qbuffer_read_only, "buffer-read-only");
  DEFSYM (Qtext_read_only, "text-read-only");
  DEFSYM (Qmark_inactive, "mark-inactive");
  DEFSYM (Qinhibited_interaction, "inhibited-interaction");

  DEFSYM (Qrecursion_error, "recursion-error");
  DEFSYM (Qexcessive_variable_binding, "excessive-variable-binding");
  DEFSYM (Qexcessive_lisp_nesting, "excessive-lisp-nesting");

  DEFSYM (Qlistp, "listp");
  DEFSYM (Qconsp, "consp");
  DEFSYM (Qsymbolp, "symbolp");
  DEFSYM (Qfixnump, "fixnump");
  DEFSYM (Qintegerp, "integerp");
  DEFSYM (Qbooleanp, "booleanp");
  DEFSYM (Qnatnump, "natnump");
  DEFSYM (Qwholenump, "wholenump");
  DEFSYM (Qstringp, "stringp");
  DEFSYM (Qarrayp, "arrayp");
  DEFSYM (Qsequencep, "sequencep");
  DEFSYM (Qbufferp, "bufferp");
  DEFSYM (Qvectorp, "vectorp");
  DEFSYM (Qrecordp, "recordp");
  DEFSYM (Qbool_vector_p, "bool-vector-p");
  DEFSYM (Qchar_or_string_p, "char-or-string-p");
  DEFSYM (Qmarkerp, "markerp");
  DEFSYM (Quser_ptrp, "user-ptrp");
  DEFSYM (Qbuffer_or_string_p, "buffer-or-string-p");
  DEFSYM (Qinteger_or_marker_p, "integer-or-marker-p");
  DEFSYM (Qfboundp, "fboundp");

  DEFSYM (Qfloatp, "floatp");
  DEFSYM (Qnumberp, "numberp");
  DEFSYM (Qnumber_or_marker_p, "number-or-marker-p");

  DEFSYM (Qchar_table_p, "char-table-p");
  DEFSYM (Qvector_or_char_table_p, "vector-or-char-table-p");
  DEFSYM (Qfixnum_or_symbol_with_pos_p, "fixnum-or-symbol-with-pos-p");
  DEFSYM (Qoclosure_interactive_form, "oclosure-interactive-form");

  DEFSYM (Qsubrp, "subrp");
  DEFSYM (Qunevalled, "unevalled");
  DEFSYM (Qmany, "many");

  DEFSYM (Qcar, "car");
  DEFSYM (Qcdr, "cdr");
  DEFSYM (Qnth, "nth");
  DEFSYM (Qelt, "elt");
  DEFSYM (Qsetcar, "setcar");
  DEFSYM (Qsetcdr, "setcdr");
  DEFSYM (Qaref, "aref");
  DEFSYM (Qaset, "aset");

  error_tail = pure_cons (Qerror, Qnil);

  /* ERROR is used as a signaler for random errors for which nothing else is
     right.  */

  Fput (Qerror, Qerror_conditions,
	error_tail);
  Fput (Qerror, Qerror_message,
	build_pure_c_string ("error"));

#define PUT_ERROR(sym, tail, msg)			\
  Fput (sym, Qerror_conditions, pure_cons (sym, tail)); \
  Fput (sym, Qerror_message, build_pure_c_string (msg))

  PUT_ERROR (Qquit, Qnil, "Quit");
  PUT_ERROR (Qminibuffer_quit, pure_cons (Qquit, Qnil), "Quit");

  PUT_ERROR (Quser_error, error_tail, "");
  PUT_ERROR (Qwrong_length_argument, error_tail, "Wrong length argument");
  PUT_ERROR (Qwrong_type_argument, error_tail, "Wrong type argument");
  PUT_ERROR (Qtype_mismatch, error_tail, "Types do not match");
  PUT_ERROR (Qargs_out_of_range, error_tail, "Args out of range");
  PUT_ERROR (Qvoid_function, error_tail,
	     "Symbol's elisp-function definition is void");
  PUT_ERROR (Qcyclic_function_indirection, error_tail,
	     "Symbol's chain of function indirections contains a loop");
  PUT_ERROR (Qcyclic_variable_indirection, error_tail,
	     "Symbol's chain of variable indirections contains a loop");
  DEFSYM (Qcircular_list, "circular-list");
  PUT_ERROR (Qcircular_list, error_tail, "List contains a loop");
  PUT_ERROR (Qvoid_variable, error_tail, "Symbol's value as variable is void");
  PUT_ERROR (Qsetting_constant, error_tail,
	     "Attempt to set a constant symbol");
  PUT_ERROR (Qtrapping_constant, error_tail,
             "Attempt to trap writes to a constant symbol");
  PUT_ERROR (Qinvalid_read_syntax, error_tail, "Invalid read syntax");
  PUT_ERROR (Qinvalid_function, error_tail, "Invalid function");
  PUT_ERROR (Qwrong_number_of_arguments, error_tail,
	     "Wrong number of arguments");
  PUT_ERROR (Qno_catch, error_tail, "No catch for tag");
  PUT_ERROR (Qend_of_file, error_tail, "End of file during parsing");

  arith_tail = pure_cons (Qarith_error, error_tail);
  Fput (Qarith_error, Qerror_conditions, arith_tail);
  Fput (Qarith_error, Qerror_message, build_pure_c_string ("Arithmetic error"));

  PUT_ERROR (Qbeginning_of_buffer, error_tail, "Beginning of buffer");
  PUT_ERROR (Qend_of_buffer, error_tail, "End of buffer");
  PUT_ERROR (Qbuffer_read_only, error_tail, "Buffer is read-only");
  PUT_ERROR (Qtext_read_only, pure_cons (Qbuffer_read_only, error_tail),
	     "Text is read-only");
  PUT_ERROR (Qinhibited_interaction, error_tail,
	     "User interaction while inhibited");

  DEFSYM (Qrange_error, "range-error");
  DEFSYM (Qdomain_error, "domain-error");
  DEFSYM (Qsingularity_error, "singularity-error");
  DEFSYM (Qoverflow_error, "overflow-error");
  DEFSYM (Qunderflow_error, "underflow-error");

  PUT_ERROR (Qdomain_error, arith_tail, "Arithmetic domain error");

  PUT_ERROR (Qrange_error, arith_tail, "Arithmetic range error");

  PUT_ERROR (Qsingularity_error, Fcons (Qdomain_error, arith_tail),
	     "Arithmetic singularity error");

  PUT_ERROR (Qoverflow_error, Fcons (Qrange_error, arith_tail),
	     "Arithmetic overflow error");
  PUT_ERROR (Qunderflow_error, Fcons (Qrange_error, arith_tail),
	     "Arithmetic underflow error");

  recursion_tail = pure_cons (Qrecursion_error, error_tail);
  Fput (Qrecursion_error, Qerror_conditions, recursion_tail);
  Fput (Qrecursion_error, Qerror_message, build_pure_c_string
	("Excessive recursive calling error"));

  PUT_ERROR (Qexcessive_lisp_nesting, recursion_tail,
	     "Lisp nesting exceeds `max-lisp-eval-depth'");
  /* Error obsolete (from 29.1), kept for compatibility.  */
  PUT_ERROR (Qexcessive_variable_binding, recursion_tail,
	     "Variable binding depth exceeds max-specpdl-size");

  /* Types that type-of returns.  */
  DEFSYM (Qboolean, "boolean");
  DEFSYM (Qinteger, "integer");
  DEFSYM (Qbignum, "bignum");
  DEFSYM (Qsymbol, "symbol");
  DEFSYM (Qstring, "string");
  DEFSYM (Qcons, "cons");
  DEFSYM (Qmarker, "marker");
  DEFSYM (Qsymbol_with_pos, "symbol-with-pos");
  DEFSYM (Qoverlay, "overlay");
  DEFSYM (Qfinalizer, "finalizer");
  DEFSYM (Qmodule_function, "module-function");
  DEFSYM (Qnative_comp_unit, "native-comp-unit");
  DEFSYM (Quser_ptr, "user-ptr");
  DEFSYM (Qfloat, "float");
  DEFSYM (Qwindow_configuration, "window-configuration");
  DEFSYM (Qprocess, "process");
  DEFSYM (Qwindow, "window");
  DEFSYM (Qsubr, "subr");
  DEFSYM (Qspecial_form, "special-form");
  DEFSYM (Qprimitive_function, "primitive-function");
  DEFSYM (Qsubr_native_elisp, "subr-native-elisp"); /* Deprecated name.  */
  DEFSYM (Qnative_comp_function, "native-comp-function");
  DEFSYM (Qbyte_code_function, "byte-code-function");
  DEFSYM (Qinterpreted_function, "interpreted-function");
  DEFSYM (Qbuffer, "buffer");
  DEFSYM (Qframe, "frame");
  DEFSYM (Qvector, "vector");
  DEFSYM (Qrecord, "record");
  DEFSYM (Qchar_table, "char-table");
  DEFSYM (Qsub_char_table, "sub-char-table");
  DEFSYM (Qbool_vector, "bool-vector");
  DEFSYM (Qhash_table, "hash-table");
  DEFSYM (Qthread, "thread");
  DEFSYM (Qmutex, "mutex");
  DEFSYM (Qcondition_variable, "condition-variable");
  DEFSYM (Qfont_spec, "font-spec");
  DEFSYM (Qfont_entity, "font-entity");
  DEFSYM (Qfont_object, "font-object");
  DEFSYM (Qterminal, "terminal");
  DEFSYM (Qxwidget, "xwidget");
  DEFSYM (Qxwidget_view, "xwidget-view");
  DEFSYM (Qtreesit_parser, "treesit-parser");
  DEFSYM (Qtreesit_node, "treesit-node");
  DEFSYM (Qtreesit_compiled_query, "treesit-compiled-query");
  DEFSYM (Qobarray, "obarray");

  DEFSYM (Qdefun, "defun");

  DEFSYM (Qdefalias_fset_function, "defalias-fset-function");
  DEFSYM (Qfunction_history, "function-history");

  DEFSYM (Qbyte_code_function_p, "byte-code-function-p");

  DEFVAR_LISP ("most-positive-fixnum", Vmost_positive_fixnum,
	       doc: /* The greatest integer that is represented efficiently.
This variable cannot be set; trying to do so will signal an error.  */);
  Vmost_positive_fixnum = make_fixnum (MOST_POSITIVE_FIXNUM);
  make_symbol_constant (intern_c_string ("most-positive-fixnum"));

  DEFVAR_LISP ("most-negative-fixnum", Vmost_negative_fixnum,
	       doc: /* The least integer that is represented efficiently.
This variable cannot be set; trying to do so will signal an error.  */);
  Vmost_negative_fixnum = make_fixnum (MOST_NEGATIVE_FIXNUM);
  make_symbol_constant (intern_c_string ("most-negative-fixnum"));

  DEFSYM (Qsymbols_with_pos_enabled, "symbols-with-pos-enabled");
  DEFVAR_BOOL ("symbols-with-pos-enabled", symbols_with_pos_enabled,
               doc: /* If non-nil, a symbol with position ordinarily behaves as its bare symbol.
Bind this to non-nil in applications such as the byte compiler.  */);
  symbols_with_pos_enabled = false;

  DEFSYM (Qwatchers, "watchers");
  DEFSYM (Qmakunbound, "makunbound");
  DEFSYM (Qunlet, "unlet");
  DEFSYM (Qset, "set");
  DEFSYM (Qset_default, "set-default");
  DEFSYM (Qcommand_modes, "command-modes");
}
