/* Evaluator for GNU Emacs Lisp interpreter.

Copyright (C) 1985-1987, 1993-1995, 1999-2019 Free Software Foundation,
Inc.

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
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include "lisp.h"
#include "blockinput.h"
#include "commands.h"
#include "keyboard.h"
#include "dispextern.h"
#include "buffer.h"

/* CACHEABLE is ordinarily nothing, except it is 'volatile' if
   necessary to cajole GCC into not warning incorrectly that a
   variable should be volatile.  */
#if defined GCC_LINT || defined lint
# define CACHEABLE volatile
#else
# define CACHEABLE /* empty */
#endif
#include "guile.h"

static void unbind_once (void *ignore);

/* Chain of condition and catch handlers currently in effect.  */

/* struct handler *handlerlist; */

/* Non-nil means record all fset's and provide's, to be undone
   if the file being autoloaded is not fully loaded.
   They are recorded by being consed onto the front of Vautoload_queue:
   (FUN . ODEF) for a defun, (0 . OFEATURES) for a provide.  */

Lisp_Object Vautoload_queue;

/* This holds either the symbol `run-hooks' or nil.
   It is nil at an early stage of startup, and when Emacs
   is shutting down.  */
Lisp_Object Vrun_hooks;

/* The commented-out variables below are macros defined in thread.h.  */

/* Current number of specbindings allocated in specpdl, not counting
   the dummy entry specpdl[-1].  */

/* ptrdiff_t specpdl_size; */

/* Pointer to beginning of specpdl.  A dummy entry specpdl[-1] exists
   only so that its address can be taken.  */

/* union specbinding *specpdl; */

/* Pointer to the dummy entry before the specpdl.  */

union specbinding *specpdl_base;

/* Pointer to first unused element in specpdl.  */

/* union specbinding *specpdl_ptr; */

/* Depth in Lisp evaluations and function calls.  */

/* static EMACS_INT lisp_eval_depth; */

/* The value of num_nonmacro_input_events as of the last time we
   started to enter the debugger.  If we decide to enter the debugger
   again when this is still equal to num_nonmacro_input_events, then we
   know that the debugger itself has an error, and we should just
   signal the error instead of entering an infinite loop of debugger
   invocations.  */

static EMACS_INT when_entered_debugger;

/* The function from which the last `signal' was called.  Set in
   Fsignal.  */
/* FIXME: We should probably get rid of this!  */
Lisp_Object Vsignaling_function;

/* If non-nil, Lisp code must not be run since some part of Emacs is in
   an inconsistent state.  Currently unused.  */
Lisp_Object inhibit_lisp_code;

static Lisp_Object funcall_lambda (Lisp_Object, ptrdiff_t, Lisp_Object *);
static Lisp_Object apply_lambda (Lisp_Object, Lisp_Object, ptrdiff_t);
static Lisp_Object lambda_arity (Lisp_Object);

static Lisp_Object
specpdl_symbol (union specbinding *pdl)
{
  eassert (pdl->kind >= SPECPDL_LET);
  return pdl->let.symbol;
}

static enum specbind_tag
specpdl_kind (union specbinding *pdl)
{
  eassert (pdl->kind >= SPECPDL_LET);
  return pdl->let.kind;
}

static Lisp_Object
specpdl_old_value (union specbinding *pdl)
{
  eassert (pdl->kind >= SPECPDL_LET);
  return pdl->let.old_value;
}

static void
set_specpdl_old_value (union specbinding *pdl, Lisp_Object val)
{
  eassert (pdl->kind >= SPECPDL_LET);
  pdl->let.old_value = val;
}

static Lisp_Object
specpdl_where (union specbinding *pdl)
{
  eassert (pdl->kind > SPECPDL_LET);
  return pdl->let.where;
}

struct handler *
make_catch_handler (Lisp_Object tag)
{
  struct handler *c = xmalloc (sizeof (*c));
  c->type = CATCHER;
  c->tag_or_ch = tag;
  c->val = Qnil;
  c->var = Qnil;
  c->body = Qnil;
  c->next = handlerlist;
  c->lisp_eval_depth = lisp_eval_depth;
  c->interrupt_input_blocked = interrupt_input_blocked;
  c->ptag = make_prompt_tag ();
  return c;
}

struct handler *
make_condition_handler (Lisp_Object tag)
{
  struct handler *c = xmalloc (sizeof (*c));
  c->type = CONDITION_CASE;
  c->tag_or_ch = tag;
  c->val = Qnil;
  c->var = Qnil;
  c->body = Qnil;
  c->next = handlerlist;
  c->lisp_eval_depth = lisp_eval_depth;
  c->interrupt_input_blocked = interrupt_input_blocked;
  c->ptag = make_prompt_tag ();
  return c;
}

static Lisp_Object eval_fn;
static Lisp_Object funcall_fn;

void
init_eval_once (void)
{
  enum { size = 50 };
  union specbinding *pdlvec = xmalloc ((size + 1) * sizeof *specpdl);
  specpdl_base = pdlvec;
  specpdl_size = size;
  specpdl = specpdl_ptr = pdlvec + 1;
  /* Don't forget to update docs (lispref node "Local Variables").  */
  max_specpdl_size = 10000; /* 1000 is not enough for CEDET's c-by.el.  */
  max_lisp_eval_depth = 10000;

  Vrun_hooks = Qnil;

  eval_fn = scm_c_public_ref ("language elisp runtime", "eval-elisp");
  funcall_fn = scm_c_public_ref ("elisp-functions", "funcall");

  //scm_set_smob_apply (lisp_vectorlike_tag, apply_lambda, 0, 0, 1);
}

static struct handler *handlerlist_sentinel;

void
init_eval (void)
{
  specpdl_ptr = specpdl;
  handlerlist_sentinel = make_catch_handler (Qunbound);
  handlerlist = handlerlist_sentinel;
  Vquit_flag = Qnil;
  debug_on_next_call = 0;
  lisp_eval_depth = 0;
  /* This is less than the initial value of num_nonmacro_input_events.  */
  when_entered_debugger = -1;
}

/* Unwind-protect function used by call_debugger.  */

static void
restore_stack_limits (Lisp_Object data)
{
  max_specpdl_size = XINT (XCAR (data));
  max_lisp_eval_depth = XINT (XCDR (data));
}

static void grow_specpdl (void);

/* Call the Lisp debugger, giving it argument ARG.  */

Lisp_Object
call_debugger (Lisp_Object arg)
{
  bool debug_while_redisplaying;
  dynwind_begin ();
  Lisp_Object val;
  EMACS_INT old_depth = max_lisp_eval_depth;
  /* Do not allow max_specpdl_size less than actual depth (Bug#16603).  */
  EMACS_INT old_max = max_specpdl_size;

  /* The previous value of 40 is too small now that the debugger
     prints using cl-prin1 instead of prin1.  Printing lists nested 8
     deep (which is the value of print-level used in the debugger)
     currently requires 77 additional frames.  See bug#31919.  */
  if (lisp_eval_depth + 100 > max_lisp_eval_depth)
    max_lisp_eval_depth = lisp_eval_depth + 100;

  /* Restore limits after leaving the debugger.  */
  record_unwind_protect (restore_stack_limits,
			 Fcons (make_number (old_max),
				make_number (old_depth)));

#ifdef HAVE_WINDOW_SYSTEM
  if (display_hourglass_p)
    cancel_hourglass ();
#endif

  debug_on_next_call = 0;
  when_entered_debugger = num_nonmacro_input_events;

  /* Resetting redisplaying_p to 0 makes sure that debug output is
     displayed if the debugger is invoked during redisplay.  */
  debug_while_redisplaying = redisplaying_p;
  redisplaying_p = 0;
  specbind (intern ("debugger-may-continue"),
	    debug_while_redisplaying ? Qnil : Qt);
  specbind (Qinhibit_redisplay, Qnil);
  specbind (Qinhibit_debugger, Qt);

  /* If we are debugging an error while `inhibit-changing-match-data'
     is bound to non-nil (e.g., within a call to `string-match-p'),
     then make sure debugger code can still use match data.  */
  specbind (Qinhibit_changing_match_data, Qnil);

#if 0 /* Binding this prevents execution of Lisp code during
	 redisplay, which necessarily leads to display problems.  */
  specbind (Qinhibit_eval_during_redisplay, Qt);
#endif

  val = apply1 (Vdebugger, arg);

  /* Interrupting redisplay and resuming it later is not safe under
     all circumstances.  So, when the debugger returns, abort the
     interrupted redisplay by going back to the top-level.  */
  if (debug_while_redisplaying)
    Ftop_level ();

  dynwind_end ();
  return val;
}

static Lisp_Object
Fprogn (Lisp_Object body)
{
  Lisp_Object val = Qnil;

  while (CONSP (body))
    {
      Lisp_Object form = XCAR (body);
      body = XCDR (body);
      val = eval_sub (form);
    }

  return val;
}

/* Evaluate BODY sequentially, discarding its value.  */

void
prog_ignore (Lisp_Object body)
{
  Fprogn (body);
}

Lisp_Object
Ffunction (Lisp_Object args)
{
  Lisp_Object quoted = XCAR (args);

  if (!NILP (XCDR (args)))
    xsignal2 (Qwrong_number_of_arguments, Qfunction, Flength (args));

  if (!NILP (Vinternal_interpreter_environment)
      && CONSP (quoted)
      && EQ (XCAR (quoted), Qlambda))
    { /* This is a lambda expression within a lexical environment;
	 return an interpreted closure instead of a simple lambda.  */
      Lisp_Object cdr = XCDR (quoted);
      Lisp_Object tmp = cdr;
      if (CONSP (tmp)
	  && (tmp = XCDR (tmp), CONSP (tmp))
	  && (tmp = XCAR (tmp), CONSP (tmp))
	  && (EQ (QCdocumentation, XCAR (tmp))))
	{ /* Handle the special (:documentation <form>) to build the docstring
	     dynamically.  */
	  Lisp_Object docstring = eval_sub (Fcar (XCDR (tmp)));
	  CHECK_STRING (docstring);
	  cdr = Fcons (XCAR (cdr), Fcons (docstring, XCDR (XCDR (cdr))));
	}
      return Fcons (Qclosure, Fcons (Vinternal_interpreter_environment,
				     cdr));
    }
  else
    /* Simply quote the argument.  */
    return quoted;
}

DEFUN ("defvaralias", Fdefvaralias, Sdefvaralias, 2, 3, 0,
       doc: /* Make NEW-ALIAS a variable alias for symbol BASE-VARIABLE.
Aliased variables always have the same value; setting one sets the other.
Third arg DOCSTRING, if non-nil, is documentation for NEW-ALIAS.  If it is
omitted or nil, NEW-ALIAS gets the documentation string of BASE-VARIABLE,
or of the variable at the end of the chain of aliases, if BASE-VARIABLE is
itself an alias.  If NEW-ALIAS is bound, and BASE-VARIABLE is not,
then the value of BASE-VARIABLE is set to that of NEW-ALIAS.
The return value is BASE-VARIABLE.  */)
  (Lisp_Object new_alias, Lisp_Object base_variable, Lisp_Object docstring)
{
  sym_t sym;

  CHECK_SYMBOL (new_alias);
  CHECK_SYMBOL (base_variable);

  if (SYMBOL_CONSTANT_P (new_alias))
    /* Making it an alias effectively changes its value.  */
    error ("Cannot make a constant an alias");

  sym = XSYMBOL (new_alias);

  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_FORWARDED:
      error ("Cannot make an internal variable an alias");
    case SYMBOL_LOCALIZED:
      error ("Don't know how to make a localized variable an alias");
    case SYMBOL_PLAINVAL:
    case SYMBOL_VARALIAS:
      break;
    default:
      emacs_abort ();
    }

  /* https://lists.gnu.org/r/emacs-devel/2008-04/msg00834.html
     If n_a is bound, but b_v is not, set the value of b_v to n_a,
     so that old-code that affects n_a before the aliasing is setup
     still works.  */
  if (NILP (Fboundp (base_variable)))
    set_internal (base_variable, find_symbol_value (new_alias),
                  Qnil, SET_INTERNAL_BIND);
  {
    union specbinding *p;

    for (p = specpdl_ptr; p > specpdl; )
      if ((--p)->kind >= SPECPDL_LET
	  && (EQ (new_alias, specpdl_symbol (p))))
	error ("Don't know how to make a let-bound variable an alias");
  }

  if (SYMBOL_CONSTANT_P(sym)) // sym->u.s.trapped_write == SYMBOL_TRAPPED_WRITE)
    notify_variable_watchers (new_alias, base_variable, Qdefvaralias, Qnil);

  SET_SYMBOL_DECLARED_SPECIAL (sym, 1);
  SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (base_variable), 1);
  SET_SYMBOL_REDIRECT (sym, SYMBOL_VARALIAS);

  SET_SYMBOL_ALIAS (sym, XSYMBOL (base_variable));
  SET_SYMBOL_CONSTANT (sym, SYMBOL_CONSTANT_P (base_variable));
  LOADHIST_ATTACH (new_alias);
  /* Even if docstring is nil: remove old docstring.  */
  Fput (new_alias, Qvariable_documentation, docstring);

  return base_variable;
}

static union specbinding *
default_toplevel_binding (Lisp_Object symbol)
{
  union specbinding *binding = NULL;
  union specbinding *pdl = specpdl_ptr;
  while (pdl > specpdl)
    {
      switch ((--pdl)->kind)
	{
	case SPECPDL_LET_DEFAULT:
	case SPECPDL_LET:
	  if (EQ (specpdl_symbol (pdl), symbol))
	    binding = pdl;
	  break;

	case SPECPDL_UNWIND:
	case SPECPDL_UNWIND_PTR:
	case SPECPDL_UNWIND_INT:
	case SPECPDL_UNWIND_VOID:
	case SPECPDL_BACKTRACE:
	case SPECPDL_LET_LOCAL:
	  break;

	default:
	  emacs_abort ();
	}
    }
  return binding;
}

DEFUN ("default-toplevel-value", Fdefault_toplevel_value, Sdefault_toplevel_value, 1, 1, 0,
       doc: /* Return SYMBOL's toplevel default value.
"Toplevel" means outside of any let binding.  */)
  (Lisp_Object symbol)
{
  union specbinding *binding = default_toplevel_binding (symbol);
  Lisp_Object value
    = binding ? specpdl_old_value (binding) : Fdefault_value (symbol);
  if (!EQ (value, Qunbound))
    return value;
  xsignal1 (Qvoid_variable, symbol);
}

DEFUN ("set-default-toplevel-value", Fset_default_toplevel_value,
       Sset_default_toplevel_value, 2, 2, 0,
       doc: /* Set SYMBOL's toplevel default value to VALUE.
"Toplevel" means outside of any let binding.  */)
     (Lisp_Object symbol, Lisp_Object value)
{
  union specbinding *binding = default_toplevel_binding (symbol);
  if (binding)
    set_specpdl_old_value (binding, value);
  else
    Fset_default (symbol, value);
  return Qnil;
}

/* Make SYMBOL lexically scoped.  */
DEFUN ("internal-make-var-non-special", Fmake_var_non_special,
       Smake_var_non_special, 1, 1, 0,
       doc: /* Internal function.  */)
     (Lisp_Object symbol)
{
  CHECK_SYMBOL (symbol);
  SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (symbol), 0);
  return Qnil;
}


DEFUN ("macroexpand", Fmacroexpand, Smacroexpand, 1, 2, 0,
       doc: /* Return result of expanding macros at top level of FORM.
If FORM is not a macro call, it is returned unchanged.
Otherwise, the macro is expanded and the expansion is considered
in place of FORM.  When a non-macro-call results, it is returned.

The second optional arg ENVIRONMENT specifies an environment of macro
definitions to shadow the loaded ones for use in file byte-compilation.  */)
  (Lisp_Object form, Lisp_Object environment)
{
  /* With cleanups from Hallvard Furuseth.  */
  register Lisp_Object expander, sym, def, tem;

  while (1)
    {
      /* Come back here each time we expand a macro call,
	 in case it expands into another macro call.  */
      if (!CONSP (form))
	break;
      /* Set SYM, give DEF and TEM right values in case SYM is not a symbol. */
      def = sym = XCAR (form);
      tem = Qnil;
      /* Trace symbols aliases to other symbols
	 until we get a symbol that is not an alias.  */
      while (SYMBOLP (def))
	{
	  maybe_quit ();
	  sym = def;
	  tem = Fassq (sym, environment);
	  if (NILP (tem))
	    {
	      def = SYMBOL_FUNCTION (sym);
	      if (!NILP (def))
		continue;
	    }
	  break;
	}
      /* Right now TEM is the result from SYM in ENVIRONMENT,
	 and if TEM is nil then DEF is SYM's function definition.  */
      if (NILP (tem))
	{
	  /* SYM is not mentioned in ENVIRONMENT.
	     Look at its function definition.  */
	  def = Fautoload_do_load (def, sym, Qmacro);
	  if (!CONSP (def))
	    /* Not defined or definition not suitable.  */
	    break;
	  if (!EQ (XCAR (def), Qmacro))
	    break;
	  else expander = XCDR (def);
	}
      else
	{
	  expander = XCDR (tem);
	  if (NILP (expander))
	    break;
	}
      {
	Lisp_Object newform = apply1 (expander, XCDR (form));
	if (EQ (form, newform))
	  break;
	else
	  form = newform;
      }
    }
  return form;
}

DEFUN ("call-with-catch", Fcatch, Scatch, 2, 2, 0,
       doc: /* Eval BODY allowing nonlocal exits using `throw'.
TAG is evalled to get the tag to use; it must not be nil.

Then the BODY is executed.
Within BODY, a call to `throw' with the same TAG exits BODY and this `catch'.
If no throw happens, `catch' returns the value of the last BODY form.
If a throw happens, it specifies the value to return from `catch'.
usage: (catch TAG BODY...)  */)
  (Lisp_Object tag, Lisp_Object thunk)
{
  return internal_catch (tag, call0, thunk);
}

/* Assert that E is true, but do not evaluate E.  Use this instead of
   eassert (E) when E contains variables that might be clobbered by a
   longjmp.  */

#define clobbered_eassert(E) verify (sizeof (E) != 0)

static void
set_handlerlist (void *data)
{
  handlerlist = data;
}

static void
restore_handler (void *data)
{
  struct handler *c = data;
  unblock_input_to (c->interrupt_input_blocked);
  immediate_quit = 0;
}

struct icc_thunk_env
{
  enum { ICC_0, ICC_1, ICC_2, ICC_3, ICC_N } type;
  union
  {
    Lisp_Object (*fun0) (void);
    Lisp_Object (*fun1) (Lisp_Object);
    Lisp_Object (*fun2) (Lisp_Object, Lisp_Object);
    Lisp_Object (*fun3) (Lisp_Object, Lisp_Object, Lisp_Object);
    Lisp_Object (*funn) (ptrdiff_t, Lisp_Object *);
  };
  union
  {
    struct
    {
      Lisp_Object arg1;
      Lisp_Object arg2;
      Lisp_Object arg3;
    };
    struct
    {
      ptrdiff_t nargs;
      Lisp_Object *args;
    };
  };
  struct handler *c;
};

static Lisp_Object
icc_thunk (void *data)
{
  Lisp_Object tem;
  struct icc_thunk_env *e = data;
  scm_dynwind_begin (0);
  scm_dynwind_unwind_handler (restore_handler, e->c, 0);
  scm_dynwind_unwind_handler (set_handlerlist,
                              handlerlist,
                              SCM_F_WIND_EXPLICITLY);
  handlerlist = e->c;
  switch (e->type)
    {
    case ICC_0:
      tem = e->fun0 ();
      break;
    case ICC_1:
      tem = e->fun1 (e->arg1);
      break;
    case ICC_2:
      tem = e->fun2 (e->arg1, e->arg2);
      break;
    case ICC_3:
      tem = e->fun3 (e->arg1, e->arg2, e->arg3);
      break;
    case ICC_N:
      tem = e->funn (e->nargs, e->args);
      break;
    default:
      emacs_abort ();
    }
  scm_dynwind_end ();
  return tem;
}

static Lisp_Object
icc_handler (void *data, Lisp_Object k, Lisp_Object v)
{
  Lisp_Object (*f) (Lisp_Object) = data;
  return f (v);
}

struct icc_handler_n_env
{
  Lisp_Object (*fun) (Lisp_Object, ptrdiff_t, Lisp_Object *);
  ptrdiff_t nargs;
  Lisp_Object *args;
};

static Lisp_Object
icc_handler_n (void *data, Lisp_Object k, Lisp_Object v)
{
  struct icc_handler_n_env *e = data;
  return e->fun (v, e->nargs, e->args);
}

static Lisp_Object
icc_lisp_handler (void *data, Lisp_Object k, Lisp_Object val)
{
  Lisp_Object tem;
  struct handler *h = data;
  Lisp_Object var = h->var;
  scm_dynwind_begin (0);
  if (!NILP (var))
    {
#if 0
      if (!NILP (Vinternal_interpreter_environment))
        specbind (Qinternal_interpreter_environment,
                  Fcons (Fcons (var, val),
                         Vinternal_interpreter_environment));
      else
#endif
        specbind (var, val);
    }
  tem = Fprogn (h->body);
  scm_dynwind_end ();
  return tem;
}

/* Set up a catch, then call C function FUNC on argument ARG.
   FUNC should return a Lisp_Object.
   This is how catches are done from within C code.  */

Lisp_Object
internal_catch (Lisp_Object tag,
		Lisp_Object (*func) (Lisp_Object), Lisp_Object arg)
{
  struct handler *c = make_catch_handler (tag);
  struct icc_thunk_env env = { .type = ICC_1,
                               .fun1 = func,
                               .arg1 = arg,
                               .c = c };
  return call_with_prompt (c->ptag,
                           make_c_closure (icc_thunk, &env, 0, 0),
                           make_c_closure (icc_handler, Fidentity, 2, 0));
}

/* Unwind the specbind, catch, and handler stacks back to CATCH, and
   jump to that CATCH, returning VALUE as the value of that catch.

   This is the guts of Fthrow and Fsignal; they differ only in the way
   they choose the catch tag to throw to.  A catch tag for a
   condition-case form has a TAG of Qnil.

   Before each catch is discarded, unbind all special bindings and
   execute all unwind-protect clauses made above that catch.  Unwind
   the handler stack as we go, so that the proper handlers are in
   effect for each unwind-protect clause we run.  At the end, restore
   some static info saved in CATCH, and longjmp to the location
   specified there.

   This is used for correct unwinding in Fthrow and Fsignal.  */

static Lisp_Object unbind_to_1 (ptrdiff_t, Lisp_Object, bool);

static _Noreturn void
unwind_to_catch (struct handler *catch, Lisp_Object value)
{
  abort_to_prompt (catch->ptag, scm_list_1 (value));
}

DEFUN ("throw", Fthrow, Sthrow, 2, 2, 0,
       doc: /* Throw to the catch for TAG and return VALUE from it.
Both TAG and VALUE are evalled.  */
       attributes: noreturn)
  (register Lisp_Object tag, Lisp_Object value)
{
  struct handler *c;

  if (!NILP (tag))
    for (c = handlerlist; c; c = c->next)
      {
	if (c->type == CATCHER_ALL)
          unwind_to_catch (c, Fcons (tag, value));
	if (c->type == CATCHER && EQ (c->tag_or_ch, tag))
	  unwind_to_catch (c, value);
      }
  xsignal2 (Qno_catch, tag, value);
}

DEFUN ("call-with-handler", Fcall_with_handler, Scall_with_handler, 4, 4, 0,
       doc: /* Regain control when an error is signaled.
Executes BODYFORM and returns its value if no error happens.
Each element of HANDLERS looks like (CONDITION-NAME BODY...)
where the BODY is made of Lisp expressions.

A handler is applicable to an error
if CONDITION-NAME is one of the error's condition names.
If an error happens, the first applicable handler is run.

The car of a handler may be a list of condition names instead of a
single condition name; then it handles all of them.  If the special
condition name `debug' is present in this list, it allows another
condition in the list to run the debugger if `debug-on-error' and the
other usual mechanisms says it should (otherwise, `condition-case'
suppresses the debugger).

When a handler handles an error, control returns to the `condition-case'
and it executes the handler's BODY...
with VAR bound to (ERROR-SYMBOL . SIGNAL-DATA) from the error.
\(If VAR is nil, the handler can't access that information.)
Then the value of the last BODY form is returned from the `condition-case'
expression.

See also the function `signal' for more info.
usage: (condition-case VAR BODYFORM &rest HANDLERS)  */)
  (Lisp_Object var,
   Lisp_Object conditions,
   Lisp_Object hthunk,
   Lisp_Object thunk)
{
  return internal_lisp_condition_case (var,
                                       list2 (intern ("funcall"), thunk),
                                       list1 (list2 (conditions, list2 (intern ("funcall"), hthunk))));
}

static Lisp_Object
ilcc1 (Lisp_Object var, Lisp_Object bodyform, Lisp_Object handlers)
{
  if (CONSP (handlers))
    {
      Lisp_Object clause = XCAR (handlers);
      Lisp_Object condition = XCAR (clause);
      Lisp_Object body = XCDR (clause);
      if (!CONSP (condition))
        condition = Fcons (condition, Qnil);
      struct handler *c = make_condition_handler (condition);
      c->var = var;
      c->body = body;
      struct icc_thunk_env env = { .type = ICC_3,
                                   .fun3 = ilcc1,
                                   .arg1 = var,
                                   .arg2 = bodyform,
                                   .arg3 = XCDR (handlers),
                                   .c = c };
      return call_with_prompt (c->ptag,
                               make_c_closure (icc_thunk, &env, 0, 0),
                               make_c_closure (icc_lisp_handler, c, 2, 0));
    }
  else
    {
      return eval_sub (bodyform);
    }
}

/* Like Fcondition_case, but the args are separate
   rather than passed in a list.  Used by Fbyte_code.  */

Lisp_Object
internal_lisp_condition_case (Lisp_Object var, Lisp_Object bodyform,
			      Lisp_Object handlers)
{
  struct handler *oldhandlerlist = handlerlist;

  CHECK_SYMBOL (var);

  for (Lisp_Object tail = handlers; CONSP (tail); tail = XCDR (tail))
    {
      Lisp_Object tem = XCAR (tail);
      if (! (NILP (tem)
	     || (CONSP (tem)
		 && (SYMBOLP (XCAR (tem))
		     || CONSP (XCAR (tem))))))
	error ("Invalid condition handler: %s",
	       SDATA (Fprin1_to_string (tem, Qt)));
    }

  return ilcc1 (var, bodyform, Freverse (handlers));
}

/* Call the function BFUN with no arguments, catching errors within it
   according to HANDLERS.  If there is an error, call HFUN with
   one argument which is the data that describes the error:
   (SIGNALNAME . DATA)

   HANDLERS can be a list of conditions to catch.
   If HANDLERS is Qt, catch all errors.
   If HANDLERS is Qerror, catch all errors
   but allow the debugger to run if that is enabled.  */

Lisp_Object
internal_condition_case (Lisp_Object (*bfun) (void), Lisp_Object handlers,
			 Lisp_Object (*hfun) (Lisp_Object))
{
  struct handler *c = make_condition_handler (handlers);

  struct icc_thunk_env env = { .type = ICC_0, .fun0 = bfun, .c = c };
  return call_with_prompt (c->ptag,
                           make_c_closure (icc_thunk, &env, 0, 0),
                           make_c_closure (icc_handler, hfun, 2, 0));
}

/* Like internal_condition_case but call BFUN with ARG as its argument.  */

Lisp_Object
internal_condition_case_1 (Lisp_Object (*bfun) (Lisp_Object), Lisp_Object arg,
			   Lisp_Object handlers,
			   Lisp_Object (*hfun) (Lisp_Object))
{
  Lisp_Object val;
  struct handler *c = make_condition_handler (handlers);

  struct icc_thunk_env env = { .type = ICC_1,
                               .fun1 = bfun,
                               .arg1 = arg,
                               .c = c };
  return call_with_prompt (c->ptag,
                           make_c_closure (icc_thunk, &env, 0, 0),
                           make_c_closure (icc_handler, hfun, 2, 0));
}

/* Like internal_condition_case_1 but call BFUN with ARG1 and ARG2 as
   its arguments.  */

Lisp_Object
internal_condition_case_2 (Lisp_Object (*bfun) (Lisp_Object, Lisp_Object),
			   Lisp_Object arg1,
			   Lisp_Object arg2,
			   Lisp_Object handlers,
			   Lisp_Object (*hfun) (Lisp_Object))
{
  struct handler *c = make_condition_handler (handlers);
  struct icc_thunk_env env = { .type = ICC_2,
                               .fun2 = bfun,
                               .arg1 = arg1,
                               .arg2 = arg2,
                               .c = c };
  return call_with_prompt (c->ptag,
                           make_c_closure (icc_thunk, &env, 0, 0),
                           make_c_closure (icc_handler, hfun, 2, 0));
}

/* Like internal_condition_case but call BFUN with NARGS as first,
   and ARGS as second argument.  */

Lisp_Object
internal_condition_case_n (Lisp_Object (*bfun) (ptrdiff_t, Lisp_Object *),
			   ptrdiff_t nargs,
			   Lisp_Object *args,
			   Lisp_Object handlers,
			   Lisp_Object (*hfun) (Lisp_Object err,
						ptrdiff_t nargs,
						Lisp_Object *args))
{
  Lisp_Object val;
  struct handler *c = make_condition_handler (handlers);

  struct icc_thunk_env env = { .type = ICC_N,
                               .funn = bfun,
                               .nargs = nargs,
                               .args = args,
                               .c = c };
  struct icc_handler_n_env henv = { .fun = hfun, .nargs = nargs, .args = args };
  return call_with_prompt (c->ptag,
                           make_c_closure (icc_thunk, &env, 0, 0),
                           make_c_closure (icc_handler_n, &henv, 2, 0));
}


static Lisp_Object signal_or_quit (Lisp_Object, Lisp_Object, bool);
static Lisp_Object find_handler_clause (Lisp_Object, Lisp_Object);
static bool maybe_call_debugger (Lisp_Object conditions, Lisp_Object sig,
				 Lisp_Object data);

static void
process_quit_flag (void)
{
  Lisp_Object flag = Vquit_flag;
  Vquit_flag = Qnil;
  if (EQ (flag, Qkill_emacs))
    Fkill_emacs (Qnil);
  if (EQ (Vthrow_on_input, flag))
    Fthrow (Vthrow_on_input, Qt);
  quit ();
}

/* Check quit-flag and quit if it is non-nil.  Typing C-g does not
   directly cause a quit; it only sets Vquit_flag.  So the program
   needs to call maybe_quit at times when it is safe to quit.  Every
   loop that might run for a long time or might not exit ought to call
   maybe_quit at least once, at a safe place.  Unless that is
   impossible, of course.  But it is very desirable to avoid creating
   loops where maybe_quit is impossible.

   If quit-flag is set to `kill-emacs' the SIGINT handler has received
   a request to exit Emacs when it is safe to do.

   When not quitting, process any pending signals.

   If you change this function, also adapt module_should_quit in
   emacs-module.c.  */

void
maybe_quit (void)
{
  if (!NILP (Vquit_flag) && NILP (Vinhibit_quit))
    process_quit_flag ();
  else if (pending_signals)
    process_pending_signals ();
}

DEFUN ("signal", Fsignal, Ssignal, 2, 2, 0,
       doc: /* Signal an error.  Args are ERROR-SYMBOL and associated DATA.
This function does not return.

An error symbol is a symbol with an `error-conditions' property
that is a list of condition names.  The symbol should be non-nil.
A handler for any of those names will get to handle this signal.
The symbol `error' should normally be one of them.

DATA should be a list.  Its elements are printed as part of the error message.
See Info anchor `(elisp)Definition of signal' for some details on how this
error message is constructed.
If the signal is handled, DATA is made available to the handler.
See also the function `condition-case'.  */
       attributes: noreturn)
  (Lisp_Object error_symbol, Lisp_Object data)
{
  /* If they call us with nonsensical arguments, produce "peculiar error".  */
  if (NILP (error_symbol) && NILP (data))
    error_symbol = Qerror;
  signal_or_quit (error_symbol, data, false);
  eassume (false);
}

/* Quit, in response to a keyboard quit request.  */
Lisp_Object
quit (void)
{
  return signal_or_quit (Qquit, Qnil, true);
}

/* Signal an error, or quit.  ERROR_SYMBOL and DATA are as with Fsignal.
   If KEYBOARD_QUIT, this is a quit; ERROR_SYMBOL should be
   Qquit and DATA should be Qnil, and this function may return.
   Otherwise this function is like Fsignal and does not return.  */

static Lisp_Object
signal_or_quit (Lisp_Object error_symbol, Lisp_Object data, bool keyboard_quit)
{
  /* When memory is full, ERROR-SYMBOL is nil,
     and DATA is (REAL-ERROR-SYMBOL . REAL-DATA).
     That is a special case--don't do this in other situations.  */
  Lisp_Object conditions;
  Lisp_Object string;
  Lisp_Object real_error_symbol
    = (NILP (error_symbol) ? Fcar (data) : error_symbol);
  Lisp_Object clause = Qnil;
  struct handler *h;

  if (waiting_for_input)
    emacs_abort ();

#if 0 /* rms: I don't know why this was here,
	 but it is surely wrong for an error that is handled.  */
#ifdef HAVE_WINDOW_SYSTEM
  if (display_hourglass_p)
    cancel_hourglass ();
#endif
#endif

  /* This hook is used by edebug.  */
  if (! NILP (Vsignal_hook_function)
      && ! NILP (error_symbol)
      /* Don't try to call a lisp function if we've already overflowed
         the specpdl stack.  */
      && specpdl_ptr < specpdl + specpdl_size)
    {
      /* Edebug takes care of restoring these variables when it exits.  */
      if (lisp_eval_depth + 20 > max_lisp_eval_depth)
	max_lisp_eval_depth = lisp_eval_depth + 20;

      if (SPECPDL_INDEX () + 40 > max_specpdl_size)
	max_specpdl_size = SPECPDL_INDEX () + 40;

      call2 (Vsignal_hook_function, error_symbol, data);
    }

  conditions = Fget (real_error_symbol, Qerror_conditions);

  for (h = handlerlist; h; h = h->next)
    {
      if (h->type != CONDITION_CASE)
	continue;
      clause = find_handler_clause (h->tag_or_ch, conditions);
      if (!NILP (clause))
	break;
    }

  if (/* Don't run the debugger for a memory-full error.
	 (There is no room in memory to do that!)  */
      !NILP (error_symbol)
      && (!NILP (Vdebug_on_signal)
	  /* If no handler is present now, try to run the debugger.  */
	  || NILP (clause)
	  /* A `debug' symbol in the handler list disables the normal
	     suppression of the debugger.  */
	  || (CONSP (clause) && !NILP (Fmemq (Qdebug, clause)))
	  /* Special handler that means "print a message and run debugger
	     if requested".  */
	  || EQ (h->tag_or_ch, Qerror)))
    {
      bool debugger_called
	= maybe_call_debugger (conditions, error_symbol, data);
      /* We can't return values to code which signaled an error, but we
	 can continue code which has signaled a quit.  */
      if (keyboard_quit && debugger_called && EQ (real_error_symbol, Qquit))
	return Qnil;
    }

  if (!NILP (clause))
    {
      Lisp_Object unwind_data
	= (NILP (error_symbol) ? data : Fcons (error_symbol, data));

      unwind_to_catch (h, unwind_data);
    }
  else
    {
      if (handlerlist != handlerlist_sentinel)
	/* FIXME: This will come right back here if there's no `top-level'
	   catcher.  A better solution would be to abort here, and instead
	   add a catch-all condition handler so we never come here.  */
	Fthrow (Qtop_level, Qt);
    }

  if (! NILP (error_symbol))
    data = Fcons (error_symbol, data);

  string = Ferror_message_string (data);
  fatal ("%s", SDATA (string));
}

/* Like xsignal, but takes 0, 1, 2, or 3 args instead of a list.  */

void
xsignal0 (Lisp_Object error_symbol)
{
  xsignal (error_symbol, Qnil);
}

void
xsignal1 (Lisp_Object error_symbol, Lisp_Object arg)
{
  xsignal (error_symbol, list1 (arg));
}

void
xsignal2 (Lisp_Object error_symbol, Lisp_Object arg1, Lisp_Object arg2)
{
  xsignal (error_symbol, list2 (arg1, arg2));
}

void
xsignal3 (Lisp_Object error_symbol, Lisp_Object arg1, Lisp_Object arg2, Lisp_Object arg3)
{
  xsignal (error_symbol, list3 (arg1, arg2, arg3));
}

/* Signal `error' with message S, and additional arg ARG.
   If ARG is not a genuine list, make it a one-element list.  */

void
signal_error (const char *s, Lisp_Object arg)
{
  Lisp_Object tortoise, hare;

  hare = tortoise = arg;
  while (CONSP (hare))
    {
      hare = XCDR (hare);
      if (!CONSP (hare))
	break;

      hare = XCDR (hare);
      tortoise = XCDR (tortoise);

      if (EQ (hare, tortoise))
	break;
    }

  if (!NILP (hare))
    arg = list1 (arg);

  xsignal (Qerror, Fcons (build_string (s), arg));
}


/* Return true if LIST is a non-nil atom or
   a list containing one of CONDITIONS.  */

static bool
wants_debugger (Lisp_Object list, Lisp_Object conditions)
{
  if (NILP (list))
    return 0;
  if (! CONSP (list))
    return 1;

  while (CONSP (conditions))
    {
      Lisp_Object this, tail;
      this = XCAR (conditions);
      for (tail = list; CONSP (tail); tail = XCDR (tail))
	if (EQ (XCAR (tail), this))
	  return 1;
      conditions = XCDR (conditions);
    }
  return 0;
}

/* Return true if an error with condition-symbols CONDITIONS,
   and described by SIGNAL-DATA, should skip the debugger
   according to debugger-ignored-errors.  */

static bool
skip_debugger (Lisp_Object conditions, Lisp_Object data)
{
  Lisp_Object tail;
  bool first_string = 1;
  Lisp_Object error_message;

  error_message = Qnil;
  for (tail = Vdebug_ignored_errors; CONSP (tail); tail = XCDR (tail))
    {
      if (STRINGP (XCAR (tail)))
	{
	  if (first_string)
	    {
	      error_message = Ferror_message_string (data);
	      first_string = 0;
	    }

	  if (fast_string_match (XCAR (tail), error_message) >= 0)
	    return 1;
	}
      else
	{
	  Lisp_Object contail;

	  for (contail = conditions; CONSP (contail); contail = XCDR (contail))
	    if (EQ (XCAR (tail), XCAR (contail)))
	      return 1;
	}
    }

  return 0;
}

/* Call the debugger if calling it is currently enabled for CONDITIONS.
   SIG and DATA describe the signal.  There are two ways to pass them:
    = SIG is the error symbol, and DATA is the rest of the data.
    = SIG is nil, and DATA is (SYMBOL . REST-OF-DATA).
      This is for memory-full errors only.  */
static bool
maybe_call_debugger (Lisp_Object conditions, Lisp_Object sig, Lisp_Object data)
{
  Lisp_Object combined_data;

  combined_data = Fcons (sig, data);

  if (
      /* Don't try to run the debugger with interrupts blocked.
	 The editing loop would return anyway.  */
      ! input_blocked_p ()
      && NILP (Vinhibit_debugger)
      /* Does user want to enter debugger for this kind of error?  */
      && (EQ (sig, Qquit)
	  ? debug_on_quit
	  : wants_debugger (Vdebug_on_error, conditions))
      && ! skip_debugger (conditions, combined_data)
      /* RMS: What's this for?  */
      && when_entered_debugger < num_nonmacro_input_events)
    {
      call_debugger (list2 (Qerror, combined_data));
      return 1;
    }

  return 0;
}

static Lisp_Object
find_handler_clause (Lisp_Object handlers, Lisp_Object conditions)
{
  register Lisp_Object h;

  /* t is used by handlers for all conditions, set up by C code.  */
  if (EQ (handlers, Qt))
    return Qt;

  /* error is used similarly, but means print an error message
     and run the debugger if that is enabled.  */
  if (EQ (handlers, Qerror))
    return Qt;

  for (h = handlers; CONSP (h); h = XCDR (h))
    {
      Lisp_Object handler = XCAR (h);
      if (!NILP (Fmemq (handler, conditions)))
	return handlers;
    }

  return Qnil;
}


/* Format and return a string; called like vprintf.  */
Lisp_Object
vformat_string (const char *m, va_list ap)
{
  char buf[4000];
  ptrdiff_t size = sizeof buf;
  ptrdiff_t size_max = STRING_BYTES_BOUND + 1;
  char *buffer = buf;
  ptrdiff_t used;
  Lisp_Object string;

  used = evxprintf (&buffer, &size, buf, size_max, m, ap);
  string = make_string (buffer, used);
  if (buffer != buf)
    xfree (buffer);

  return string;
}

/* Dump an error message; called like vprintf.  */
void
verror (const char *m, va_list ap)
{
  xsignal1 (Qerror, vformat_string (m, ap));
}


/* Dump an error message; called like printf.  */

/* VARARGS 1 */
void
error (const char *m, ...)
{
  va_list ap;
  va_start (ap, m);
  verror (m, ap);
}

DEFUN ("commandp", Fcommandp, Scommandp, 1, 2, 0,
       doc: /* Non-nil if FUNCTION makes provisions for interactive calling.
This means it contains a description for how to read arguments to give it.
The value is nil for an invalid function or a symbol with no function
definition.

Interactively callable functions include strings and vectors (treated
as keyboard macros), lambda-expressions that contain a top-level call
to `interactive', autoload definitions made by `autoload' with non-nil
fourth argument, and some of the built-in functions of Lisp.

Also, a symbol satisfies `commandp' if its function definition does so.

If the optional argument FOR-CALL-INTERACTIVELY is non-nil,
then strings and vectors are not accepted.  */)
  (Lisp_Object function, Lisp_Object for_call_interactively)
{
  register Lisp_Object fun;
  register Lisp_Object funcar;
  Lisp_Object if_prop = Qnil;

  fun = function;

  fun = indirect_function (fun); /* Check cycles.  */
  if (NILP (fun))
    return Qnil;

  /* Check an `interactive-form' property if present, analogous to the
     function-documentation property.  */
  fun = function;
  while (SYMBOLP (fun))
    {
      Lisp_Object tmp = Fget (fun, Qinteractive_form);
      if (!NILP (tmp))
	if_prop = Qt;
      fun = Fsymbol_function (fun);
    }

  if (scm_is_true (scm_procedure_p (fun)))
    return (scm_is_pair (scm_assq (Qinteractive_form,
                                   scm_procedure_properties (fun)))
            ? Qt : if_prop);
  /* Bytecode objects are interactive if they are long enough to
     have an element whose index is COMPILED_INTERACTIVE, which is
     where the interactive spec is stored.  */
  else if (COMPILEDP (fun))
    return (PVSIZE (fun) > COMPILED_INTERACTIVE ? Qt : if_prop);

  /* Strings and vectors are keyboard macros.  */
  if (STRINGP (fun) || VECTORP (fun))
    return (NILP (for_call_interactively) ? Qt : Qnil);

  /* Lists may represent commands.  */
  if (!CONSP (fun))
    return Qnil;
  funcar = XCAR (fun);
  if (EQ (funcar, Qclosure))
    return (!NILP (Fassq (Qinteractive, Fcdr (Fcdr (XCDR (fun)))))
	    ? Qt : if_prop);
  else if (EQ (funcar, Qlambda))
    return !NILP (Fassq (Qinteractive, Fcdr (XCDR (fun)))) ? Qt : if_prop;
  else if (EQ (funcar, Qautoload))
    return !NILP (Fcar (Fcdr (Fcdr (XCDR (fun))))) ? Qt : if_prop;
  else
    return Qnil;
}

DEFUN ("autoload", Fautoload, Sautoload, 2, 5, 0,
       doc: /* Define FUNCTION to autoload from FILE.
FUNCTION is a symbol; FILE is a file name string to pass to `load'.
Third arg DOCSTRING is documentation for the function.
Fourth arg INTERACTIVE if non-nil says function can be called interactively.
Fifth arg TYPE indicates the type of the object:
   nil or omitted says FUNCTION is a function,
   `keymap' says FUNCTION is really a keymap, and
   `macro' or t says FUNCTION is really a macro.
Third through fifth args give info about the real definition.
They default to nil.
If FUNCTION is already defined other than as an autoload,
this does nothing and returns nil.  */)
  (Lisp_Object function, Lisp_Object file, Lisp_Object docstring, Lisp_Object interactive, Lisp_Object type)
{
  CHECK_SYMBOL (function);
  CHECK_STRING (file);

  /* If function is defined and not as an autoload, don't override.  */
  if (!NILP (SYMBOL_FUNCTION (function))
      && !AUTOLOADP (SYMBOL_FUNCTION (function)))
    return Qnil;

  return Fdefalias (function,
		    list5 (Qautoload, file, docstring, interactive, type),
		    Qnil);
}

void
un_autoload (Lisp_Object oldqueue)
{
  Lisp_Object queue, first, second;

  /* Queue to unwind is current value of Vautoload_queue.
     oldqueue is the shadowed value to leave in Vautoload_queue.  */
  queue = Vautoload_queue;
  Vautoload_queue = oldqueue;
  while (CONSP (queue))
    {
      first = XCAR (queue);
      second = Fcdr (first);
      first = Fcar (first);
      if (EQ (first, make_number (0)))
	Vfeatures = second;
      else
	Ffset (first, second);
      queue = XCDR (queue);
    }
}

/* Load an autoloaded function.
   FUNNAME is the symbol which is the function's name.
   FUNDEF is the autoload definition (a list).  */

DEFUN ("autoload-do-load", Fautoload_do_load, Sautoload_do_load, 1, 3, 0,
       doc: /* Load FUNDEF which should be an autoload.
If non-nil, FUNNAME should be the symbol whose function value is FUNDEF,
in which case the function returns the new autoloaded function value.
If equal to `macro', MACRO-ONLY specifies that FUNDEF should only be loaded if
it defines a macro.  */)
  (Lisp_Object fundef, Lisp_Object funname, Lisp_Object macro_only)
{
  dynwind_begin ();

  if (!CONSP (fundef) || !EQ (Qautoload, XCAR (fundef))) {
    dynwind_end ();
    return fundef;
  }

  if (EQ (macro_only, Qmacro))
    {
      Lisp_Object kind = Fnth (make_number (4), fundef);
      if (! (EQ (kind, Qt) || EQ (kind, Qmacro))) {
        dynwind_end ();
        return fundef;
      }
    }

  /* This is to make sure that loadup.el gives a clear picture
     of what files are preloaded and when.  */
  /*if (! NILP (Vpurify_flag))
    error ("Attempt to autoload %s while preparing to dump",
    SDATA (SYMBOL_NAME (funname)));*/

  CHECK_SYMBOL (funname);

  /* Preserve the match data.  */
  record_unwind_save_match_data ();

  /* If autoloading gets an error (which includes the error of failing
     to define the function being called), we use Vautoload_queue
     to undo function definitions and `provide' calls made by
     the function.  We do this in the specific case of autoloading
     because autoloading is not an explicit request "load this file",
     but rather a request to "call this function".

     The value saved here is to be restored into Vautoload_queue.  */
  record_unwind_protect (un_autoload, Vautoload_queue);
  Vautoload_queue = Qt;
  /* If `macro_only', assume this autoload to be a "best-effort",
     so don't signal an error if autoloading fails.  */
  Fload (Fcar (Fcdr (fundef)), macro_only, Qt, Qnil, Qt);

  /* Once loading finishes, don't undo it.  */
  Vautoload_queue = Qt;
  dynwind_end ();

  if (NILP (funname))
    return Qnil;
  else
    {
      Lisp_Object fun = Findirect_function (funname, Qnil);

      if (!NILP (Fequal (fun, fundef)))
	error ("Autoloading file %s failed to define function %s",
	       SDATA (Fcar (Fcar (Vload_history))),
	       SDATA (SYMBOL_NAME (funname)));
      else
	return fun;
    }
}


DEFUN ("eval", Feval, Seval, 1, 2, 0,
       doc: /* Evaluate FORM and return its value.
If LEXICAL is t, evaluate using lexical scoping.
LEXICAL can also be an actual lexical environment, in the form of an
alist mapping symbols to their value.  */)
  (Lisp_Object form, Lisp_Object lexical)
{
  dynwind_begin ();
  specbind (Qinternal_interpreter_environment,
	    CONSP (lexical) || NILP (lexical) ? lexical : list1 (Qt));
  Lisp_Object tem0 = eval_sub (form);
  dynwind_end ();
  return tem0;
}

/* Grow the specpdl stack by one entry.
   The caller should have already initialized the entry.
   Signal an error on stack overflow.

   Make sure that there is always one unused entry past the top of the
   stack, so that the just-initialized entry is safely unwound if
   memory exhausted and an error is signaled here.  Also, allocate a
   never-used entry just before the bottom of the stack; sometimes its
   address is taken.  */

static void
grow_specpdl (void)
{
  specpdl_ptr++;

  if (specpdl_ptr == specpdl + specpdl_size)
    {
      ptrdiff_t count = SPECPDL_INDEX ();
      ptrdiff_t max_size = min (max_specpdl_size, PTRDIFF_MAX - 1000);
      union specbinding *pdlvec = specpdl - 1;
      ptrdiff_t pdlvecsize = specpdl_size + 1;
      if (max_size <= specpdl_size)
	{
	  if (max_specpdl_size < 400)
	    max_size = max_specpdl_size = 400;
	  if (max_size <= specpdl_size)
	    signal_error ("Variable binding depth exceeds max-specpdl-size",
			  Qnil);
	}
      pdlvec = xpalloc (pdlvec, &pdlvecsize, 1, max_size + 1, sizeof *specpdl);
      specpdl_base = pdlvec;
      specpdl = pdlvec + 1;
      specpdl_size = pdlvecsize - 1;
      specpdl_ptr = specpdl + count;
    }
}

static void
set_lisp_eval_depth (void *data)
{
  EMACS_INT n = (EMACS_INT) data;
  lisp_eval_depth = n;
}

/* Eval a sub-expression of the current expression (i.e. in the same
   lexical scope).  */
static Lisp_Object
eval_sub_1 (Lisp_Object form)
{
  QUIT; // FIX: 20190626 LAV, really needed?
  return scm_call_1 (eval_fn, form);
}

Lisp_Object
eval_sub (Lisp_Object form)
{
  return scm_c_value_ref (eval_sub_1 (form), 0);
}

static Lisp_Object
values_to_list (Lisp_Object values)
{
  Lisp_Object list = Qnil;
  for (int i = scm_c_nvalues (values) - 1; i >= 0; i--)
    list = Fcons (scm_c_value_ref (values, i), list);
  return list;
}

DEFUN ("multiple-value-call", Fmultiple_value_call, Smultiple_value_call,
       2, UNEVALLED, 0,
       doc: /* Call with multiple values.
usage: (multiple-value-call FUNCTION-FORM FORM)  */)
  (Lisp_Object args)
{
  Lisp_Object function_form = eval_sub (XCAR (args));
  Lisp_Object values = Qnil;
  while (CONSP (args = XCDR (args)))
    values = nconc2 (Fnreverse (values_to_list (eval_sub_1 (XCAR (args)))),
                     values);
  return apply1 (function_form, Fnreverse (values));
}

DEFUN ("values", Fvalues, Svalues, 0, MANY, 0,
       doc: /* Return multiple values. */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  return scm_c_values (args, nargs);
}

Lisp_Object
Fapply (ptrdiff_t nargs, Lisp_Object *args)
{
  ptrdiff_t i, numargs, funcall_nargs;
  register Lisp_Object *funcall_args = NULL;
  register Lisp_Object spread_arg = args[nargs - 1];
  Lisp_Object fun = args[0];
  Lisp_Object retval;
  USE_SAFE_ALLOCA;

  CHECK_LIST (spread_arg);

  numargs = XINT (Flength (spread_arg));

  if (numargs == 0)
    return Ffuncall (nargs - 1, args);
  else if (numargs == 1)
    {
      args [nargs - 1] = XCAR (spread_arg);
      return Ffuncall (nargs, args);
    }

  numargs += nargs - 2;

  /* Optimize for no indirection.  */
  if (SYMBOLP (fun) && !NILP (fun)
      && (fun = SYMBOL_FUNCTION (fun), SYMBOLP (fun)))
    fun = indirect_function (fun);
  if (NILP (fun))
    {
      /* Let funcall get the error.  */
      fun = args[0];
    }

  /* We add 1 to numargs because funcall_args includes the
     function itself as well as its arguments.  */
  if (!funcall_args)
    {
      SAFE_ALLOCA_LISP (funcall_args, 1 + numargs);
      funcall_nargs = 1 + numargs;
    }

  memcpy (funcall_args, args, nargs * word_size);
  /* Spread the last arg we got.  Its first element goes in
     the slot that it used to occupy, hence this value of I.  */
  i = nargs - 1;
  while (!NILP (spread_arg))
    {
      funcall_args [i++] = XCAR (spread_arg);
      spread_arg = XCDR (spread_arg);
    }

  retval = Ffuncall (funcall_nargs, funcall_args);

  SAFE_FREE ();
  return retval;
}

/* Run hook variables in various ways.  */

static Lisp_Object
funcall_nil (ptrdiff_t nargs, Lisp_Object *args)
{
  Ffuncall (nargs, args);
  return Qnil;
}

DEFUN ("run-hooks", Frun_hooks, Srun_hooks, 0, MANY, 0,
       doc: /* Run each hook in HOOKS.
Each argument should be a symbol, a hook variable.
These symbols are processed in the order specified.
If a hook symbol has a non-nil value, that value may be a function
or a list of functions to be called to run the hook.
If the value is a function, it is called with no arguments.
If it is a list, the elements are called, in order, with no arguments.

Major modes should not use this function directly to run their mode
hook; they should use `run-mode-hooks' instead.

Do not use `make-local-variable' to make a hook variable buffer-local.
Instead, use `add-hook' and specify t for the LOCAL argument.
usage: (run-hooks &rest HOOKS)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  ptrdiff_t i;

  for (i = 0; i < nargs; i++)
    run_hook (args[i]);

  return Qnil;
}

DEFUN ("run-hook-with-args", Frun_hook_with_args,
       Srun_hook_with_args, 1, MANY, 0,
       doc: /* Run HOOK with the specified arguments ARGS.
HOOK should be a symbol, a hook variable.  The value of HOOK
may be nil, a function, or a list of functions.  Call each
function in order with arguments ARGS.  The final return value
is unspecified.

Do not use `make-local-variable' to make a hook variable buffer-local.
Instead, use `add-hook' and specify t for the LOCAL argument.
usage: (run-hook-with-args HOOK &rest ARGS)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  return run_hook_with_args (nargs, args, funcall_nil);
}

/* NB this one still documents a specific non-nil return value.
   (As did run-hook-with-args and run-hook-with-args-until-failure
   until they were changed in 24.1.)  */
DEFUN ("run-hook-with-args-until-success", Frun_hook_with_args_until_success,
       Srun_hook_with_args_until_success, 1, MANY, 0,
       doc: /* Run HOOK with the specified arguments ARGS.
HOOK should be a symbol, a hook variable.  The value of HOOK
may be nil, a function, or a list of functions.  Call each
function in order with arguments ARGS, stopping at the first
one that returns non-nil, and return that value.  Otherwise (if
all functions return nil, or if there are no functions to call),
return nil.

Do not use `make-local-variable' to make a hook variable buffer-local.
Instead, use `add-hook' and specify t for the LOCAL argument.
usage: (run-hook-with-args-until-success HOOK &rest ARGS)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  return run_hook_with_args (nargs, args, Ffuncall);
}

static Lisp_Object
funcall_not (ptrdiff_t nargs, Lisp_Object *args)
{
  return NILP (Ffuncall (nargs, args)) ? Qt : Qnil;
}

DEFUN ("run-hook-with-args-until-failure", Frun_hook_with_args_until_failure,
       Srun_hook_with_args_until_failure, 1, MANY, 0,
       doc: /* Run HOOK with the specified arguments ARGS.
HOOK should be a symbol, a hook variable.  The value of HOOK
may be nil, a function, or a list of functions.  Call each
function in order with arguments ARGS, stopping at the first
one that returns nil, and return nil.  Otherwise (if all functions
return non-nil, or if there are no functions to call), return non-nil
\(do not rely on the precise return value in this case).

Do not use `make-local-variable' to make a hook variable buffer-local.
Instead, use `add-hook' and specify t for the LOCAL argument.
usage: (run-hook-with-args-until-failure HOOK &rest ARGS)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  return NILP (run_hook_with_args (nargs, args, funcall_not)) ? Qt : Qnil;
}

static Lisp_Object
run_hook_wrapped_funcall (ptrdiff_t nargs, Lisp_Object *args)
{
  Lisp_Object tmp = args[0], ret;
  args[0] = args[1];
  args[1] = tmp;
  ret = Ffuncall (nargs, args);
  args[1] = args[0];
  args[0] = tmp;
  return ret;
}

DEFUN ("run-hook-wrapped", Frun_hook_wrapped, Srun_hook_wrapped, 2, MANY, 0,
       doc: /* Run HOOK, passing each function through WRAP-FUNCTION.
I.e. instead of calling each function FUN directly with arguments ARGS,
it calls WRAP-FUNCTION with arguments FUN and ARGS.
As soon as a call to WRAP-FUNCTION returns non-nil, `run-hook-wrapped'
aborts and returns that value.
usage: (run-hook-wrapped HOOK WRAP-FUNCTION &rest ARGS)  */)
     (ptrdiff_t nargs, Lisp_Object *args)
{
  return run_hook_with_args (nargs, args, run_hook_wrapped_funcall);
}

/* ARGS[0] should be a hook symbol.
   Call each of the functions in the hook value, passing each of them
   as arguments all the rest of ARGS (all NARGS - 1 elements).
   FUNCALL specifies how to call each function on the hook.  */

Lisp_Object
run_hook_with_args (ptrdiff_t nargs, Lisp_Object *args,
		    Lisp_Object (*funcall) (ptrdiff_t nargs, Lisp_Object *args))
{
  Lisp_Object sym, val, ret = Qnil;

  /* If we are dying or still initializing,
     don't do anything--it would probably crash if we tried.  */
  if (NILP (Vrun_hooks))
    return Qnil;

  sym = args[0];
  val = find_symbol_value (sym);

  if (EQ (val, Qunbound) || NILP (val))
    return ret;
  else if (!CONSP (val) || FUNCTIONP (val))
    {
      args[0] = val;
      return funcall (nargs, args);
    }
  else
    {
      Lisp_Object global_vals = Qnil;

      for (;
	   CONSP (val) && NILP (ret);
	   val = XCDR (val))
	{
	  if (EQ (XCAR (val), Qt))
	    {
	      /* t indicates this hook has a local binding;
		 it means to run the global binding too.  */
	      global_vals = Fdefault_value (sym);
	      if (NILP (global_vals)) continue;

	      if (!CONSP (global_vals) || EQ (XCAR (global_vals), Qlambda))
		{
		  args[0] = global_vals;
		  ret = funcall (nargs, args);
		}
	      else
		{
		  for (;
		       CONSP (global_vals) && NILP (ret);
		       global_vals = XCDR (global_vals))
		    {
		      args[0] = XCAR (global_vals);
		      /* In a global value, t should not occur.  If it does, we
			 must ignore it to avoid an endless loop.  */
		      if (!EQ (args[0], Qt))
			ret = funcall (nargs, args);
		    }
		}
	    }
	  else
	    {
	      args[0] = XCAR (val);
	      ret = funcall (nargs, args);
	    }
	}

      return ret;
    }
}

/* Run the hook HOOK, giving each function no args.  */

void
run_hook (Lisp_Object hook)
{
  Frun_hook_with_args (1, &hook);
}

/* Run the hook HOOK, giving each function the two args ARG1 and ARG2.  */

void
run_hook_with_args_2 (Lisp_Object hook, Lisp_Object arg1, Lisp_Object arg2)
{
  CALLN (Frun_hook_with_args, hook, arg1, arg2);
}

/* Apply fn to arg.  */
Lisp_Object
apply1 (Lisp_Object fn, Lisp_Object arg)
{
  return NILP (arg) ? Ffuncall (1, &fn) : CALLN (Fapply, fn, arg);
}

/* Call function fn on no arguments.  */
Lisp_Object
call0 (Lisp_Object fn)
{
  return Ffuncall (1, &fn);
}

/* Call function fn with 1 argument arg1.  */
/* ARGSUSED */
Lisp_Object
call1 (Lisp_Object fn, Lisp_Object arg1)
{
  return CALLN (Ffuncall, fn, arg1);
}

/* Call function fn with 2 arguments arg1, arg2.  */
/* ARGSUSED */
Lisp_Object
call2 (Lisp_Object fn, Lisp_Object arg1, Lisp_Object arg2)
{
  return CALLN (Ffuncall, fn, arg1, arg2);
}

/* Call function fn with 3 arguments arg1, arg2, arg3.  */
/* ARGSUSED */
Lisp_Object
call3 (Lisp_Object fn, Lisp_Object arg1, Lisp_Object arg2, Lisp_Object arg3)
{
  return CALLN (Ffuncall, fn, arg1, arg2, arg3);
}

/* Call function fn with 4 arguments arg1, arg2, arg3, arg4.  */
/* ARGSUSED */
Lisp_Object
call4 (Lisp_Object fn, Lisp_Object arg1, Lisp_Object arg2, Lisp_Object arg3,
       Lisp_Object arg4)
{
  return CALLN (Ffuncall, fn, arg1, arg2, arg3, arg4);
}

/* Call function fn with 5 arguments arg1, arg2, arg3, arg4, arg5.  */
/* ARGSUSED */
Lisp_Object
call5 (Lisp_Object fn, Lisp_Object arg1, Lisp_Object arg2, Lisp_Object arg3,
       Lisp_Object arg4, Lisp_Object arg5)
{
  return CALLN (Ffuncall, fn, arg1, arg2, arg3, arg4, arg5);
}

/* Call function fn with 6 arguments arg1, arg2, arg3, arg4, arg5, arg6.  */
/* ARGSUSED */
Lisp_Object
call6 (Lisp_Object fn, Lisp_Object arg1, Lisp_Object arg2, Lisp_Object arg3,
       Lisp_Object arg4, Lisp_Object arg5, Lisp_Object arg6)
{
  return CALLN (Ffuncall, fn, arg1, arg2, arg3, arg4, arg5, arg6);
}

/* Call function fn with 7 arguments arg1, arg2, arg3, arg4, arg5, arg6, arg7.  */
/* ARGSUSED */
Lisp_Object
call7 (Lisp_Object fn, Lisp_Object arg1, Lisp_Object arg2, Lisp_Object arg3,
       Lisp_Object arg4, Lisp_Object arg5, Lisp_Object arg6, Lisp_Object arg7)
{
  return CALLN (Ffuncall, fn, arg1, arg2, arg3, arg4, arg5, arg6, arg7);
}

/* Call function fn with 8 arguments arg1, arg2, arg3, arg4, arg5,
   arg6, arg7, arg8.  */
/* ARGSUSED */
Lisp_Object
call8 (Lisp_Object fn, Lisp_Object arg1, Lisp_Object arg2, Lisp_Object arg3,
       Lisp_Object arg4, Lisp_Object arg5, Lisp_Object arg6, Lisp_Object arg7,
       Lisp_Object arg8)
{
  return CALLN (Ffuncall, fn, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8);
}

DEFUN ("functionp", Ffunctionp, Sfunctionp, 1, 1, 0,
       doc: /* Return t if OBJECT is a function.  */)
     (Lisp_Object object)
{
  if (FUNCTIONP (object))
    return Qt;
  return Qnil;
}

static Lisp_Object
Ffuncall1 (ptrdiff_t nargs, Lisp_Object *args)
{
  return scm_call_n (funcall_fn, args, nargs);
}

Lisp_Object
Ffuncall (ptrdiff_t nargs, Lisp_Object *args)
{
  return scm_c_value_ref (Ffuncall1 (nargs, args), 0);
}


/* Apply a C subroutine SUBR to the NUMARGS evaluated arguments in ARG_VECTOR
   and return the result of evaluation.  */

Lisp_Object
funcall_subr (struct Lisp_Subr *subr, ptrdiff_t numargs, Lisp_Object *args)
{
  if (numargs < subr->min_args
      || (subr->max_args >= 0 && subr->max_args < numargs))
    {
      Lisp_Object fun;
      XSETSUBR (fun, subr);
      xsignal2 (Qwrong_number_of_arguments, fun, make_number (numargs));
    }

  else if (subr->max_args == UNEVALLED)
    {
      Lisp_Object fun;
      XSETSUBR (fun, subr);
      xsignal1 (Qinvalid_function, fun);
    }

  else if (subr->max_args == MANY)
    return (subr->function.aMANY) (numargs, args);
  else
    {
      Lisp_Object internal_argbuf[8];
      Lisp_Object *internal_args;
      if (subr->max_args > numargs)
        {
          eassert (subr->max_args <= ARRAYELTS (internal_argbuf));
          internal_args = internal_argbuf;
          memcpy (internal_args, args, numargs * word_size);
          memclear (internal_args + numargs,
                    (subr->max_args - numargs) * word_size);
        }
      else
        internal_args = args;
      switch (subr->max_args)
        {
        case 0:
          return (subr->function.a0 ());
        case 1:
          return (subr->function.a1 (internal_args[0]));
        case 2:
          return (subr->function.a2
                  (internal_args[0], internal_args[1]));
        case 3:
          return (subr->function.a3
                  (internal_args[0], internal_args[1], internal_args[2]));
        case 4:
          return (subr->function.a4
                  (internal_args[0], internal_args[1], internal_args[2],
                   internal_args[3]));
        case 5:
          return (subr->function.a5
                  (internal_args[0], internal_args[1], internal_args[2],
                   internal_args[3], internal_args[4]));
        case 6:
          return (subr->function.a6
                  (internal_args[0], internal_args[1], internal_args[2],
                   internal_args[3], internal_args[4], internal_args[5]));
        case 7:
          return (subr->function.a7
                  (internal_args[0], internal_args[1], internal_args[2],
                   internal_args[3], internal_args[4], internal_args[5],
                   internal_args[6]));
        case 8:
          return (subr->function.a8
                  (internal_args[0], internal_args[1], internal_args[2],
                   internal_args[3], internal_args[4], internal_args[5],
                   internal_args[6], internal_args[7]));

        default:

          /* If a subr takes more than 8 arguments without using MANY
             or UNEVALLED, we need to extend this function to support it.
             Until this is done, there is no way to call the function.  */
          emacs_abort ();
        }
    }
}

static Lisp_Object
apply_lambda (Lisp_Object fun, Lisp_Object args, ptrdiff_t count)
{
  Lisp_Object args_left;
  ptrdiff_t i;
  EMACS_INT numargs;
  Lisp_Object *arg_vector;
  Lisp_Object tem;
  USE_SAFE_ALLOCA;

  numargs = XFASTINT (Flength (args));
  SAFE_ALLOCA_LISP (arg_vector, numargs);
  args_left = args;

  for (i = 0; i < numargs; )
    {
      tem = Fcar (args_left), args_left = Fcdr (args_left);
      arg_vector[i++] = tem;
    }

  tem = funcall_lambda (fun, numargs, arg_vector);

  SAFE_FREE ();
  specpdl_ptr--; //FIX: 20190627 LAV, dont think this is used?
  return tem;
}

/* Apply a Lisp function FUN to the NARGS evaluated arguments in ARG_VECTOR
   and return the result of evaluation.
   FUN must be either a lambda-expression, a compiled-code object,
   or a module function.  */

static Lisp_Object
funcall_lambda (Lisp_Object fun, ptrdiff_t nargs,
		register Lisp_Object *arg_vector)
{
  Lisp_Object val, syms_left, next, lexenv;
  dynwind_begin ();
  ptrdiff_t i;
  bool optional, rest;

  if (CONSP (fun))
    {
      if (EQ (XCAR (fun), Qclosure))
	{
	  Lisp_Object cdr = XCDR (fun);	/* Drop `closure'.  */
	  if (! CONSP (cdr))
	    xsignal1 (Qinvalid_function, fun);
	  fun = cdr;
	  lexenv = XCAR (fun);
	}
      else
	lexenv = Qnil;
      syms_left = XCDR (fun);
      if (CONSP (syms_left))
	syms_left = XCAR (syms_left);
      else
	xsignal1 (Qinvalid_function, fun);
    }
#ifdef HAVE_MODULES
  else if (MODULE_FUNCTIONP (fun))
    return funcall_module (fun, nargs, arg_vector);
#endif
  else
    emacs_abort ();

  i = optional = rest = 0;
  bool previous_optional_or_rest = false;
  for (; CONSP (syms_left); syms_left = XCDR (syms_left))
    {
      maybe_quit ();

      next = XCAR (syms_left);
      if (!SYMBOLP (next))
	xsignal1 (Qinvalid_function, fun);

      if (EQ (next, Qand_rest))
        {
          if (rest || previous_optional_or_rest)
            xsignal1 (Qinvalid_function, fun);
          rest = 1;
          previous_optional_or_rest = true;
        }
      else if (EQ (next, Qand_optional))
        {
          if (optional || rest || previous_optional_or_rest)
            xsignal1 (Qinvalid_function, fun);
          optional = 1;
          previous_optional_or_rest = true;
        }
      else
	{
	  Lisp_Object arg;
	  if (rest)
	    {
	      arg = Flist (nargs - i, &arg_vector[i]);
	      i = nargs;
	    }
	  else if (i < nargs)
	    arg = arg_vector[i++];
	  else if (!optional)
	    xsignal2 (Qwrong_number_of_arguments, fun, make_number (nargs));
	  else
	    arg = Qnil;

	  /* Bind the argument.  */
	  if (!NILP (lexenv) && SYMBOLP (next))
	    /* Lexically bind NEXT by adding it to the lexenv alist.  */
	    lexenv = Fcons (Fcons (next, arg), lexenv);
	  else
	    /* Dynamically bind NEXT.  */
	    specbind (next, arg);
          previous_optional_or_rest = false;
	}
    }

  if (!NILP (syms_left) || previous_optional_or_rest)
    xsignal1 (Qinvalid_function, fun);
  else if (i < nargs)
    xsignal2 (Qwrong_number_of_arguments, fun, make_number (nargs));

  if (!EQ (lexenv, Vinternal_interpreter_environment))
    /* Instantiate a new lexical environment.  */
    specbind (Qinternal_interpreter_environment, lexenv);

  val = Fprogn (XCDR (XCDR (fun)));

  dynwind_end ();
  return val;
}

DEFUN ("func-arity", Ffunc_arity, Sfunc_arity, 1, 1, 0,
       doc: /* Return minimum and maximum number of args allowed for FUNCTION.
FUNCTION must be a function of some kind.
The returned value is a cons cell (MIN . MAX).  MIN is the minimum number
of args.  MAX is the maximum number, or the symbol `many', for a
function with `&rest' args, or `unevalled' for a special form.  */)
  (Lisp_Object function)
{
  Lisp_Object original;
  Lisp_Object funcar;
  Lisp_Object result;

  original = function;

 retry:

  /* Optimize for no indirection.  */
  function = original;
  if (SYMBOLP (function) && !NILP (function))
    {
      function = XSYMBOL (function)->u.s.function;
      if (SYMBOLP (function))
	function = indirect_function (function);
    }

  if (CONSP (function) && EQ (XCAR (function), Qmacro))
    function = XCDR (function);

  if (SUBRP (function))
    result = Fsubr_arity (function);
  else if (COMPILEDP (function))
    result = lambda_arity (function);
#ifdef HAVE_MODULES
  else if (MODULE_FUNCTIONP (function))
    result = module_function_arity (XMODULE_FUNCTION (function));
#endif
  else
    {
      if (NILP (function))
	xsignal1 (Qvoid_function, original);
      if (!CONSP (function))
	xsignal1 (Qinvalid_function, original);
      funcar = XCAR (function);
      if (!SYMBOLP (funcar))
	xsignal1 (Qinvalid_function, original);
      if (EQ (funcar, Qlambda)
	  || EQ (funcar, Qclosure))
	result = lambda_arity (function);
      else if (EQ (funcar, Qautoload))
	{
	  Fautoload_do_load (function, original, Qnil);
	  goto retry;
	}
      else
	xsignal1 (Qinvalid_function, original);
    }
  return result;
}

/* FUN must be either a lambda-expression or a compiled-code object.  */
static Lisp_Object
lambda_arity (Lisp_Object fun)
{
  Lisp_Object syms_left;

  if (CONSP (fun))
    {
      if (EQ (XCAR (fun), Qclosure))
	{
	  fun = XCDR (fun);	/* Drop `closure'.  */
	  CHECK_CONS (fun);
	}
      syms_left = XCDR (fun);
      if (CONSP (syms_left))
	syms_left = XCAR (syms_left);
      else
	xsignal1 (Qinvalid_function, fun);
    }
  else if (COMPILEDP (fun))
    {
      ptrdiff_t size = PVSIZE (fun);
      if (size <= COMPILED_STACK_DEPTH)
	xsignal1 (Qinvalid_function, fun);
      syms_left = AREF (fun, COMPILED_ARGLIST);
      if (INTEGERP (syms_left))
        return get_byte_code_arity (syms_left);
    }
  else
    emacs_abort ();

  EMACS_INT minargs = 0, maxargs = 0;
  bool optional = false;
  for (; CONSP (syms_left); syms_left = XCDR (syms_left))
    {
      Lisp_Object next = XCAR (syms_left);
      if (!SYMBOLP (next))
	xsignal1 (Qinvalid_function, fun);

      if (EQ (next, Qand_rest))
	return Fcons (make_number (minargs), Qmany);
      else if (EQ (next, Qand_optional))
	optional = true;
      else
	{
          if (!optional)
            minargs++;
          maxargs++;
        }
    }

  if (!NILP (syms_left))
    xsignal1 (Qinvalid_function, fun);

  return Fcons (make_number (minargs), make_number (maxargs));
}

DEFUN ("fetch-bytecode", Ffetch_bytecode, Sfetch_bytecode,
       1, 1, 0,
       doc: /* If byte-compiled OBJECT is lazy-loaded, fetch it now.  */)
  (Lisp_Object object)
{
  Lisp_Object tem;

  if (COMPILEDP (object))
    {
      ptrdiff_t size = PVSIZE (object);
      if (size <= COMPILED_STACK_DEPTH)
	xsignal1 (Qinvalid_function, object);
      if (CONSP (AREF (object, COMPILED_BYTECODE)))
	{
	  tem = read_doc_string (AREF (object, COMPILED_BYTECODE));
	  if (!CONSP (tem))
	    {
	      tem = AREF (object, COMPILED_BYTECODE);
	      if (CONSP (tem) && STRINGP (XCAR (tem)))
		error ("Invalid byte code in %s", SDATA (XCAR (tem)));
	      else
		error ("Invalid byte code");
	    }
	  ASET (object, COMPILED_BYTECODE, XCAR (tem));
	  ASET (object, COMPILED_CONSTANTS, XCDR (tem));
	}
    }
  return object;
}

/* Return true if SYMBOL currently has a let-binding
   which was made in the buffer that is now current.  */

bool
let_shadows_buffer_binding_p (sym_t symbol)
{
  union specbinding *p;
  Lisp_Object buf = Fcurrent_buffer ();

  for (p = specpdl_ptr; p > specpdl; )
    if ((--p)->kind > SPECPDL_LET)
      {
	sym_t let_bound_symbol = XSYMBOL (specpdl_symbol (p));
	eassert (SYMBOL_REDIRECT (let_bound_symbol) != SYMBOL_VARALIAS);
	if (symbol == let_bound_symbol
	    && EQ (specpdl_where (p), buf))
	  return 1;
      }

  return 0;
}

static void
do_specbind (struct Lisp_Symbol *sym, union specbinding *bind,
             Lisp_Object value, enum Set_Internal_Bind bindflag)
{
  switch (sym->u.s.redirect)
    {
    case SYMBOL_PLAINVAL:
      if (!sym->u.s.trapped_write)
	SET_SYMBOL_VAL (sym, value);
      else
        set_internal (specpdl_symbol (bind), value, Qnil, bindflag);
      break;

    case SYMBOL_FORWARDED:
      if (BUFFER_OBJFWDP (SYMBOL_FWD (sym))
	  && specpdl_kind (bind) == SPECPDL_LET_DEFAULT)
	{
          set_default_internal (specpdl_symbol (bind), value, bindflag);
	  return;
	}
      FALLTHROUGH;
    case SYMBOL_LOCALIZED:
      set_internal (specpdl_symbol (bind), value, Qnil, bindflag);
      break;

    default:
      emacs_abort ();
    }
}

/* `specpdl_ptr' describes which variable is
   let-bound, so it can be properly undone when we unbind_to.
   It can be either a plain SPECPDL_LET or a SPECPDL_LET_LOCAL/DEFAULT.
   - SYMBOL is the variable being bound.  Note that it should not be
     aliased (i.e. when let-binding V1 that's aliased to V2, we want
     to record V2 here).
   - WHERE tells us in which buffer the binding took place.
     This is used for SPECPDL_LET_LOCAL bindings (i.e. bindings to a
     buffer-local variable) as well as for SPECPDL_LET_DEFAULT bindings,
     i.e. bindings to the default value of a variable which can be
     buffer-local.  */

void
specbind (Lisp_Object symbol, Lisp_Object value)
{
  sym_t sym;

  CHECK_SYMBOL (symbol);
  sym = XSYMBOL (symbol);

 start:
  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_VARALIAS:
      sym = indirect_variable (sym); XSETSYMBOL (symbol, sym); goto start;
    case SYMBOL_PLAINVAL:
      /* The most common case is that of a non-constant symbol with a
	 trivial value.  Make that as fast as we can.  */
      specpdl_ptr->let.kind = SPECPDL_LET;
      specpdl_ptr->let.symbol = symbol;
      specpdl_ptr->let.old_value = SYMBOL_VAL (sym);
      specpdl_ptr->let.saved_value = Qnil;
      grow_specpdl ();
      do_specbind (sym, specpdl_ptr - 1, value, SET_INTERNAL_BIND);
      break;
    case SYMBOL_LOCALIZED:
    case SYMBOL_FORWARDED:
      {
	Lisp_Object ovalue = find_symbol_value (symbol);
	specpdl_ptr->let.kind = SPECPDL_LET_LOCAL;
	specpdl_ptr->let.symbol = symbol;
	specpdl_ptr->let.old_value = ovalue;
	specpdl_ptr->let.where = Fcurrent_buffer ();
	specpdl_ptr->let.saved_value = Qnil;

	eassert (SYMBOL_REDIRECT (sym) != SYMBOL_LOCALIZED
		 || (EQ (SYMBOL_BLV (sym)->where, Fcurrent_buffer ())));

	if (SYMBOL_REDIRECT (sym) == SYMBOL_LOCALIZED)
	  {
	    if (!blv_found (SYMBOL_BLV (sym)))
	      specpdl_ptr->let.kind = SPECPDL_LET_DEFAULT;
	  }
	else if (BUFFER_OBJFWDP (SYMBOL_FWD (sym)))
	  {
	    /* If SYMBOL is a per-buffer variable which doesn't have a
	       buffer-local value here, make the `let' change the global
	       value by changing the value of SYMBOL in all buffers not
	       having their own value.  This is consistent with what
	       happens with other buffer-local variables.  */
	    if (NILP (Flocal_variable_p (symbol, Qnil)))
	      {
		specpdl_ptr->let.kind = SPECPDL_LET_DEFAULT;
		grow_specpdl ();
                do_specbind (sym, specpdl_ptr - 1, value, SET_INTERNAL_BIND);
		goto done;
	      }
	  }
	else
	  specpdl_ptr->let.kind = SPECPDL_LET;

	grow_specpdl ();
        do_specbind (sym, specpdl_ptr - 1, value, SET_INTERNAL_BIND);
	break;
      }
    default: emacs_abort ();
    }

 done:
  scm_dynwind_unwind_handler (unbind_once, NULL, SCM_F_WIND_EXPLICITLY);
}

/* Push unwind-protect entries of various types.  */

void
record_unwind_protect_1 (void (*function) (Lisp_Object), Lisp_Object arg,
                         bool wind_explicitly)
{
  record_unwind_protect_ptr_1 (function, arg, wind_explicitly);
}

void
record_unwind_protect (void (*function) (Lisp_Object), Lisp_Object arg)
{
  record_unwind_protect_1 (function, arg, true);
}

void
record_unwind_protect_ptr_1 (void (*function) (void *), void *arg,
                             bool wind_explicitly)
{
  scm_dynwind_unwind_handler (function,
                              arg,
                              (wind_explicitly
                               ? SCM_F_WIND_EXPLICITLY
                               : 0));
}

void
record_unwind_protect_ptr (void (*function) (void *), void *arg)
{
  record_unwind_protect_ptr_1 (function, arg, true);
}

void
rebind_for_thread_switch (void)
{
  union specbinding *bind;

  for (bind = specpdl; bind != specpdl_ptr; ++bind)
    {
      if (bind->kind >= SPECPDL_LET)
	{
	  Lisp_Object value = specpdl_saved_value (bind);
	  Lisp_Object sym = specpdl_symbol (bind);
	  bind->let.saved_value = Qnil;
          do_specbind (XSYMBOL (sym), bind, value,
                       SET_INTERNAL_THREAD_SWITCH);
	}
    }
}

static void
do_one_unbind (union specbinding *this_binding, bool unwinding,
               enum Set_Internal_Bind bindflag)
{
  eassert (unwinding || this_binding->kind >= SPECPDL_LET);
  switch (this_binding->kind)
    {
    case SPECPDL_UNWIND:
      this_binding->unwind.func (this_binding->unwind.arg);
      break;
    case SPECPDL_UNWIND_PTR:
      this_binding->unwind_ptr.func (this_binding->unwind_ptr.arg);
      break;
    case SPECPDL_UNWIND_INT:
      this_binding->unwind_int.func (this_binding->unwind_int.arg);
      break;
    case SPECPDL_UNWIND_VOID:
      this_binding->unwind_void.func ();
      break;
    case SPECPDL_BACKTRACE:
      break;
    case SPECPDL_LET:
      { /* If variable has a trivial value (no forwarding), and isn't
	   trapped, we can just set it.  */
	Lisp_Object sym = specpdl_symbol (this_binding);
	if (SYMBOLP (sym) && XSYMBOL (sym)->u.s.redirect == SYMBOL_PLAINVAL)
	  {
	    if (XSYMBOL (sym)->u.s.trapped_write == SYMBOL_UNTRAPPED_WRITE)
	      SET_SYMBOL_VAL (XSYMBOL (sym), specpdl_old_value (this_binding));
	    else
	      set_internal (sym, specpdl_old_value (this_binding),
                            Qnil, bindflag);
	    break;
	  }
      }
      /* Come here only if make_local_foo was used for the first time
	 on this var within this let.  */
      FALLTHROUGH;
    case SPECPDL_LET_DEFAULT:
      set_default_internal (specpdl_symbol (this_binding),
                            specpdl_old_value (this_binding),
                            bindflag);
      break;
    case SPECPDL_LET_LOCAL:
      {
	Lisp_Object symbol = specpdl_symbol (this_binding);
	Lisp_Object where = specpdl_where (this_binding);
	Lisp_Object old_value = specpdl_old_value (this_binding);
	eassert (BUFFERP (where));

	/* If this was a local binding, reset the value in the appropriate
	   buffer, but only if that buffer's binding still exists.  */
	if (!NILP (Flocal_variable_p (symbol, where)))
          set_internal (symbol, old_value, where, bindflag);
      }
      break;
    }
}

static void
do_nothing (void)
{}



/* Push an unwind-protect entry that does nothing, so that
   set_unwind_protect_ptr can overwrite it later.  */

void
record_unwind_protect_int_1 (void (*function) (int), int arg,
                             bool wind_explicitly)
{
  record_unwind_protect_ptr_1 (function, arg, wind_explicitly);
}

void
record_unwind_protect_int (void (*function) (int), int arg)
{
  record_unwind_protect_int_1 (function, arg, true);
}

static void
call_void (void *data)
{
  ((void (*) (void)) data) ();
}

void
record_unwind_protect_void_1 (void (*function) (void),
                              bool wind_explicitly)
{
  record_unwind_protect_ptr_1 (call_void, function, wind_explicitly);
}

void
record_unwind_protect_void (void (*function) (void))
{
  record_unwind_protect_void_1 (function, true);
}

static void
unbind_once (void *ignore)
{
  /* Decrement specpdl_ptr before we do the work to unbind it, so
     that an error in unbinding won't try to unbind the same entry
     again.  Take care to copy any parts of the binding needed
     before invoking any code that can make more bindings.  */

  specpdl_ptr--;

  switch (specpdl_ptr->kind)
    {
    case SPECPDL_LET:
      { /* If variable has a trivial value (no forwarding), we can
           just set it.  No need to check for constant symbols here,
           since that was already done by specbind.  */
        sym_t sym = XSYMBOL (specpdl_symbol (specpdl_ptr));
        if (SYMBOL_REDIRECT (sym) == SYMBOL_PLAINVAL)
          {
            SET_SYMBOL_VAL (sym, specpdl_old_value (specpdl_ptr));
            break;
          }
        else
          { /* FALLTHROUGH!!
               NOTE: we only ever come here if make_local_foo was used for
               the first time on this var within this let.  */
          }
      }
    case SPECPDL_LET_DEFAULT:
      Fset_default (specpdl_symbol (specpdl_ptr),
                    specpdl_old_value (specpdl_ptr));
      break;
    case SPECPDL_LET_LOCAL:
      {
        Lisp_Object symbol = specpdl_symbol (specpdl_ptr);
        Lisp_Object where = specpdl_where (specpdl_ptr);
        Lisp_Object old_value = specpdl_old_value (specpdl_ptr);
        eassert (BUFFERP (where));

        /* If this was a local binding, reset the value in the appropriate
           buffer, but only if that buffer's binding still exists.  */
        if (!NILP (Flocal_variable_p (symbol, where)))
          set_internal (symbol, old_value, where, 1);
      }
      break;
    }
}

void
dynwind_begin (void)
{
  scm_dynwind_begin (0);
}

void
dynwind_end (void)
{
  scm_dynwind_end ();
}

DEFUN ("special-variable-p", Fspecial_variable_p, Sspecial_variable_p, 1, 1, 0,
       doc: /* Return non-nil if SYMBOL's global binding has been declared special.
A special variable is one that will be bound dynamically, even in a
context where binding is lexical by default.  */)
  (Lisp_Object symbol)
{
   CHECK_SYMBOL (symbol);
   return SYMBOL_DECLARED_SPECIAL (XSYMBOL (symbol)) ? Qt : Qnil;
}


_Noreturn SCM
abort_to_prompt (SCM tag, SCM arglst)
{
  static SCM var = SCM_UNDEFINED;
  if (SCM_UNBNDP (var))
    var = scm_c_public_lookup ("guile", "abort-to-prompt");

  scm_apply_1 (scm_variable_ref (var), tag, arglst);
  emacs_abort ();
}

SCM
call_with_prompt (SCM tag, SCM thunk, SCM handler)
{
  static SCM var = SCM_UNDEFINED;
  if (SCM_UNBNDP (var))
    var = scm_c_public_lookup ("guile", "call-with-prompt");

  return scm_call_3 (scm_variable_ref (var), tag, thunk, handler);
}

SCM
make_prompt_tag (void)
{
  static SCM var = SCM_UNDEFINED;
  if (SCM_UNBNDP (var))
    var = scm_c_public_lookup ("guile", "make-prompt-tag");

  return scm_call_0 (scm_variable_ref (var));
}

void
syms_of_eval (void)
{
#include "eval.x"

  DEFVAR_INT ("max-specpdl-size", max_specpdl_size,
	      doc: /* Limit on number of Lisp variable bindings and `unwind-protect's.
If Lisp code tries to increase the total number past this amount,
an error is signaled.
You can safely use a value considerably larger than the default value,
if that proves inconveniently small.  However, if you increase it too far,
Emacs could run out of memory trying to make the stack bigger.
Note that this limit may be silently increased by the debugger
if `debug-on-error' or `debug-on-quit' is set.  */);

  DEFVAR_INT ("max-lisp-eval-depth", max_lisp_eval_depth,
	      doc: /* Limit on depth in `eval', `apply' and `funcall' before error.

This limit serves to catch infinite recursions for you before they cause
actual stack overflow in C, which would be fatal for Emacs.
You can safely make it considerably larger than its default value,
if that proves inconveniently small.  However, if you increase it too far,
Emacs could overflow the real C stack, and crash.  */);

  DEFVAR_LISP ("quit-flag", Vquit_flag,
	       doc: /* Non-nil causes `eval' to abort, unless `inhibit-quit' is non-nil.
If the value is t, that means do an ordinary quit.
If the value equals `throw-on-input', that means quit by throwing
to the tag specified in `throw-on-input'; it's for handling `while-no-input'.
Typing C-g sets `quit-flag' to t, regardless of `inhibit-quit',
but `inhibit-quit' non-nil prevents anything from taking notice of that.  */);
  Vquit_flag = Qnil;

  DEFVAR_LISP ("inhibit-quit", Vinhibit_quit,
	       doc: /* Non-nil inhibits C-g quitting from happening immediately.
Note that `quit-flag' will still be set by typing C-g,
so a quit will be signaled as soon as `inhibit-quit' is nil.
To prevent this happening, set `quit-flag' to nil
before making `inhibit-quit' nil.  */);
  Vinhibit_quit = Qnil;

  DEFSYM (Qsetq, "setq");
  DEFSYM (Qinhibit_quit, "inhibit-quit");
  DEFSYM (Qautoload, "autoload");
  DEFSYM (Qinhibit_debugger, "inhibit-debugger");
  DEFSYM (Qmacro, "macro");

  /* Note that the process handling also uses Qexit, but we don't want
     to staticpro it twice, so we just do it here.  */
  DEFSYM (Qexit, "exit");

  DEFSYM (Qinteractive, "interactive");
  DEFSYM (Qcommandp, "commandp");
  DEFSYM (Qand_rest, "&rest");
  DEFSYM (Qand_optional, "&optional");
  DEFSYM (Qclosure, "closure");
  DEFSYM (QCdocumentation, ":documentation");
  DEFSYM (Qdebug, "debug");

  DEFVAR_LISP ("inhibit-debugger", Vinhibit_debugger,
	       doc: /* Non-nil means never enter the debugger.
Normally set while the debugger is already active, to avoid recursive
invocations.  */);
  Vinhibit_debugger = Qnil;

  DEFVAR_LISP ("debug-on-error", Vdebug_on_error,
	       doc: /* Non-nil means enter debugger if an error is signaled.
Does not apply to errors handled by `condition-case' or those
matched by `debug-ignored-errors'.
If the value is a list, an error only means to enter the debugger
if one of its condition symbols appears in the list.
When you evaluate an expression interactively, this variable
is temporarily non-nil if `eval-expression-debug-on-error' is non-nil.
The command `toggle-debug-on-error' toggles this.
See also the variable `debug-on-quit' and `inhibit-debugger'.  */);
  Vdebug_on_error = Qnil;

  DEFVAR_LISP ("debug-ignored-errors", Vdebug_ignored_errors,
    doc: /* List of errors for which the debugger should not be called.
Each element may be a condition-name or a regexp that matches error messages.
If any element applies to a given error, that error skips the debugger
and just returns to top level.
This overrides the variable `debug-on-error'.
It does not apply to errors handled by `condition-case'.  */);
  Vdebug_ignored_errors = Qnil;

  DEFVAR_BOOL ("debug-on-quit", debug_on_quit,
    doc: /* Non-nil means enter debugger if quit is signaled (C-g, for example).
Does not apply if quit is handled by a `condition-case'.  */);
  debug_on_quit = 0;

  DEFVAR_BOOL ("debug-on-next-call", debug_on_next_call,
	       doc: /* Non-nil means enter debugger before next `eval', `apply' or `funcall'.  */);

  DEFVAR_BOOL ("debugger-may-continue", debugger_may_continue,
	       doc: /* Non-nil means debugger may continue execution.
This is nil when the debugger is called under circumstances where it
might not be safe to continue.  */);
  debugger_may_continue = 1;

  DEFVAR_BOOL ("debugger-stack-frame-as-list", debugger_stack_frame_as_list,
	       doc: /* Non-nil means display call stack frames as lists. */);
  debugger_stack_frame_as_list = 0;

  DEFVAR_LISP ("debugger", Vdebugger,
	       doc: /* Function to call to invoke debugger.
If due to frame exit, args are `exit' and the value being returned;
 this function's value will be returned instead of that.
If due to error, args are `error' and a list of the args to `signal'.
If due to `apply' or `funcall' entry, one arg, `lambda'.
If due to `eval' entry, one arg, t.  */);
  Vdebugger = Qnil;

  DEFVAR_LISP ("signal-hook-function", Vsignal_hook_function,
	       doc: /* If non-nil, this is a function for `signal' to call.
It receives the same arguments that `signal' was given.
The Edebug package uses this to regain control.  */);
  Vsignal_hook_function = Qnil;

  DEFVAR_LISP ("debug-on-signal", Vdebug_on_signal,
	       doc: /* Non-nil means call the debugger regardless of condition handlers.
Note that `debug-on-error', `debug-on-quit' and friends
still determine whether to handle the particular condition.  */);
  Vdebug_on_signal = Qnil;

  /* When lexical binding is being used,
   Vinternal_interpreter_environment is non-nil, and contains an alist
   of lexically-bound variable, or (t), indicating an empty
   environment.  The lisp name of this variable would be
   `internal-interpreter-environment' if it weren't hidden.
   Every element of this list can be either a cons (VAR . VAL)
   specifying a lexical binding, or a single symbol VAR indicating
   that this variable should use dynamic scoping.  */
  DEFSYM (Qinternal_interpreter_environment,
	  "internal-interpreter-environment");
  DEFVAR_LISP ("internal-interpreter-environment",
		Vinternal_interpreter_environment,
	       doc: /* If non-nil, the current lexical environment of the lisp interpreter.
When lexical binding is not being used, this variable is nil.
A value of `(t)' indicates an empty environment, otherwise it is an
alist of active lexical bindings.  */);
  Vinternal_interpreter_environment = Qnil;
  /* Don't export this variable to Elisp, so no one can mess with it
     (Just imagine if someone makes it buffer-local).  */
  //Funintern (Qinternal_interpreter_environment, Qnil);

  Vrun_hooks = intern_c_string ("run-hooks");
  staticpro (&Vrun_hooks);

  staticpro (&Vautoload_queue);
  Vautoload_queue = Qnil;
  staticpro (&Vsignaling_function);
  Vsignaling_function = Qnil;

  inhibit_lisp_code = Qnil;

  DEFSYM (Qdefvaralias, "defvaralias");
  DEFSYM (QCdebug_on_exit, ":debug-on-exit");
}
