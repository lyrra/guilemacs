/* Evaluator for GNU Emacs Lisp interpreter.

Copyright (C) 1985-1987, 1993-1995, 1999-2025 Free Software Foundation,
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
#include <stdlib.h>
#include "lisp.h"
#include "guile.h"
#include "blockinput.h"
#include "commands.h"
#include "keyboard.h"
#include "dispextern.h"
#include "buffer.h"
#include "atimer.h"

uint64_t scheme_to_c_crossings;
uint64_t c_to_scheme_crossings;

static void unbind_guile (void *data);

/* Non-nil means record all fset's and provide's, to be undone
   if the file being autoloaded is not fully loaded.
   They are recorded by being consed onto the front of Vautoload_queue:
   (FUN . ODEF) for a defun, (0 . OFEATURES) for a provide.  */

Lisp_Object Vautoload_queue;

/* This holds either the symbol `run-hooks' or nil.
   It is nil at an early stage of startup, and when Emacs
   is shutting down.  */
Lisp_Object Vrun_hooks;

/* The function from which the last `signal' was called.  Set in
   Fsignal.  */
/* FIXME: We should probably get rid of this!  */
Lisp_Object Vsignaling_function;

/* Symbol used for Guile-based condition handling.
   All elisp errors are thrown to this key.  */
static SCM elisp_condition_sym = SCM_BOOL_F;

/* Symbol used for Guile-based catch/throw.
   All elisp throws use this key, with the actual tag in the args.  */
static SCM elisp_throw_sym = SCM_BOOL_F;

/* Scheme binding registry functions */
static SCM push_binding_fn = SCM_BOOL_F;
static SCM pop_binding_fn = SCM_BOOL_F;
static SCM symbol_lexbound_fn = SCM_BOOL_F;
static SCM let_shadows_buffer_binding_fn = SCM_BOOL_F;
static SCM symbol_has_binding_fn = SCM_BOOL_F;

static Lisp_Object funcall_lambda (Lisp_Object, ptrdiff_t, Lisp_Object *);
static Lisp_Object lambda_arity (Lisp_Object);

static Lisp_Object eval_fn;
static Lisp_Object funcall_fn;

void
init_eval_once (void)
{
  /* Don't forget to update docs (lispref node "Eval").
   * - 1000 is not enough for CEDET's c-by.el.
   * - 1500 is not enough for cl-generic.el.
   * - 1800 See bug#46818.
   * - 2500; 1600; Original values increased for comp.el.
   *
   */
  max_lisp_eval_depth = 10000;
  Vrun_hooks = Qnil;

  current_thread->m_thread_alive = true;

  eval_fn = scm_c_public_ref ("emacs-elisp runtime", "eval-elisp");
  funcall_fn = scm_c_public_ref ("elisp-functions", "funcall");

  /* Initialize symbols for Guile-based exception handling */
  elisp_condition_sym = scm_from_utf8_symbol ("elisp-condition");
  elisp_throw_sym = scm_from_utf8_symbol ("elisp-throw");

  //scm_set_smob_apply (lisp_vectorlike_tag, apply_lambda, 0, 0, 1);
}

void
init_eval (void)
{
  Vquit_flag = Qnil;
  debug_on_next_call = 0;
  lisp_eval_depth = 0;
  /* This is less than the initial value of num_nonmacro_input_events.  */
  when_entered_debugger = -1;
}

static void
restore_stack_limits (Lisp_Object data)
{
  intmax_t old_depth;
  integer_to_intmax (data, &old_depth);
  lisp_eval_depth_reserve += max_lisp_eval_depth - old_depth;
  max_lisp_eval_depth = old_depth;
}

/* Try and ensure that we have at least B dpeth available.  */

static void
max_ensure_room (intmax_t b)
{
  intmax_t sum = ckd_add (&sum, lisp_eval_depth, b) ? INTMAX_MAX : sum;
  intmax_t diff = min (sum - max_lisp_eval_depth, lisp_eval_depth_reserve);
  if (diff <= 0)
    return;
  intmax_t old_depth = max_lisp_eval_depth;
  max_lisp_eval_depth += diff;
  lisp_eval_depth_reserve -= diff;
  /* Restore limits after leaving the debugger.  */
  record_unwind_protect (restore_stack_limits, make_int (old_depth));
}

/* Call the Lisp debugger, giving it argument ARG.  */

Lisp_Object
call_debugger (Lisp_Object arg)
{
  bool debug_while_redisplaying;
  dynwind_begin ();
  Lisp_Object val;

  /* The previous value of 40 is too small now that the debugger
     prints using cl-prin1 instead of prin1.  Printing lists nested 8
     deep (which is the value of print-level used in the debugger)
     currently requires 77 additional frames.  See bug#31919.  */
  max_ensure_room (100);

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
  specbind_guile (Qdebugger_may_continue,
	    debug_while_redisplaying ? Qnil : Qt);
  specbind_guile (Qinhibit_redisplay, Qnil);
  specbind_guile (Qinhibit_debugger, Qt);

  /* If we are debugging an error while `inhibit-changing-match-data'
     is bound to non-nil (e.g., within a call to `string-match-p'),
     then make sure debugger code can still use match data.  */
  specbind_guile (Qinhibit_changing_match_data, Qnil);

#if 0 /* Binding this prevents execution of Lisp code during
	 redisplay, which necessarily leads to display problems.  */
  specbind_guile (Qinhibit_eval_during_redisplay, Qt);
#endif

  val = apply1 (Vdebugger, arg);

  /* Interrupting redisplay and resuming it later is not safe under
     all circumstances.  So, when the debugger returns, abort the
     interrupted redisplay by going back to the top-level.  */
  /* FIXME: Move this to the redisplay code?  */
  if (debug_while_redisplaying
      && !EQ (Vdebugger, Qdebug_early))
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

DEFUN ("defvaralias", Fdefvaralias, Sdefvaralias, 2, 3, 0,
       doc: /* Make NEW-ALIAS a variable alias for symbol BASE-VARIABLE.
Aliased variables always have the same value; setting one sets the other.
Third arg DOCSTRING, if non-nil, is documentation for NEW-ALIAS.  If it is
omitted or nil, NEW-ALIAS gets the documentation string of BASE-VARIABLE,
or of the variable at the end of the chain of aliases, if BASE-VARIABLE is
itself an alias.  If NEW-ALIAS is bound, and BASE-VARIABLE is not,
then the value of BASE-VARIABLE is set to that of NEW-ALIAS.
The return value is BASE-VARIABLE.

If the resulting chain of variable definitions would contain a loop,
signal a `cyclic-variable-indirection' error.  */)
  (Lisp_Object new_alias, Lisp_Object base_variable, Lisp_Object docstring)
{
  CHECK_SYMBOL (new_alias);
  CHECK_SYMBOL (base_variable);

  if (SYMBOL_CONSTANT_P (new_alias))
    /* Making it an alias effectively changes its value.  */
    error ("Cannot make a constant an alias: %s",
	   SDATA (SYMBOL_NAME (new_alias)));

  sym_t sym = XSYMBOL (new_alias);

  /* Ensure non-circularity.  */
  Lisp_Object s = XSYMBOL (base_variable);
  for (;;)
    {
      if (s == sym)
	xsignal1 (Qcyclic_variable_indirection, base_variable);
      if (SYMBOL_REDIRECT(s) != SYMBOL_VARALIAS)
	break;
      s = SYMBOL_ALIAS (s);
    }

  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_FORWARDED:
      error ("Cannot make a built-in variable an alias: %s",
	     SDATA (SYMBOL_NAME (new_alias)));
    case SYMBOL_LOCALIZED:
      error ("Don't know how to make a buffer-local variable an alias: %s",
	     SDATA (SYMBOL_NAME (new_alias)));
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
  else if (!NILP (Fboundp (new_alias))
           && !EQ (find_symbol_value (new_alias),
                   find_symbol_value (base_variable)))
    {
      Lisp_Object message, formatted;

      message = build_string ("Overwriting value of `%s' by aliasing"
			      " to `%s'");
      formatted = CALLN (Fformat_message, message,
			 new_alias, base_variable);
      call2 (Qdisplay_warning,
	     list3 (Qdefvaralias, Qlosing_value, new_alias),
	     formatted);
    }

  /* Check if symbol is let-bound using Scheme binding registry (Phase 3).  */
  {
    if (scm_is_false (symbol_has_binding_fn))
      symbol_has_binding_fn = scm_c_public_ref ("emacs bindings", "symbol-has-binding?");
    if (!scm_is_false (scm_call_1 (symbol_has_binding_fn, new_alias)))
      error ("Don't know how to make a let-bound variable an alias: %s",
	     SDATA (SYMBOL_NAME (new_alias)));
  }

  // fix guilemacs, no Qdefvaralias, rebase error?
  //if (SYMBOL_TRAPPED (sym) == SYMBOL_TRAPPED_WRITE)
  //  notify_variable_watchers (new_alias, base_variable, Qdefvaralias, Qnil);

  SET_SYMBOL_DECLARED_SPECIAL (sym, 1);
  SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (base_variable), 1);
  SET_SYMBOL_REDIRECT (sym, SYMBOL_VARALIAS);
  SET_SYMBOL_ALIAS (sym, XSYMBOL (base_variable));
  SET_SYMBOL_TRAPPED (sym, SYMBOL_TRAPPED (XSYMBOL (base_variable)));
  LOADHIST_ATTACH (new_alias);
  /* Even if docstring is nil: remove old docstring.  */
  Fput (new_alias, Qvariable_documentation, docstring);

  return base_variable;
}

/* Look for a lexical-binding of SYMBOL somewhere up the stack.
   This will only find bindings created with interpreted code, since once
   compiled names of lexical variables are basically gone anyway.  */
static bool
lexbound_p (Lisp_Object symbol)
{
  /* Use Scheme binding registry for introspection.  */
  if (scm_is_false (symbol_lexbound_fn))
    symbol_lexbound_fn = scm_c_public_ref ("emacs bindings", "symbol-lexbound?");
  return !scm_is_false (scm_call_1 (symbol_lexbound_fn, symbol));
}

DEFUNWRAP1(Fdefault_toplevel_value, "default-toplevel-value")
DEFUNWRAP1(Fset_default_toplevel_value, "set-default-toplevel-value")

DEFUN ("internal--define-uninitialized-variable",
       Finternal__define_uninitialized_variable,
       Sinternal__define_uninitialized_variable, 1, 2, 0,
       doc: /* Define SYMBOL as a variable, with DOC as its docstring.
This is like `defvar' and `defconst' but without affecting the variable's
value.  */)
  (Lisp_Object symbol, Lisp_Object doc)
{
  if (!SYMBOL_DECLARED_SPECIAL (XSYMBOL (symbol))
      && lexbound_p (symbol))
    /* This test tries to catch the situation where we do
       (let ((<foo-var> ...)) ...(<foo-function> ...)....)
       and where the `foo` package only gets loaded when <foo-function>
       is called, so the outer `let` incorrectly made the binding lexical
       because the <foo-var> wasn't yet declared as dynamic at that point.  */
    xsignal2 (Qerror,
	      build_string ("Defining as dynamic an already lexical var"),
	      symbol);

  SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (symbol), 1);
  if (!NILP (doc))
    {
      if (!NILP (Vpurify_flag))
	doc = Fpurecopy (doc);
      Fput (symbol, Qvariable_documentation, doc);
    }
  LOADHIST_ATTACH (symbol);
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


static void
with_delayed_message_display (struct atimer *timer)
{
  message3 (build_string (timer->client_data));
}

static void
with_delayed_message_cancel (void *timer)
{
  xfree (((struct atimer *) timer)->client_data);
  cancel_atimer (timer);
}

DEFUN ("funcall-with-delayed-message",
       Ffuncall_with_delayed_message, Sfuncall_with_delayed_message,
       3, 3, 0,
       doc: /* Like `funcall', but display MESSAGE if FUNCTION takes longer than TIMEOUT.
TIMEOUT is a number of seconds, and can be an integer or a floating
point number.

If FUNCTION takes less time to execute than TIMEOUT seconds, MESSAGE
is not displayed.  */)
  (Lisp_Object timeout, Lisp_Object message, Lisp_Object function)
{
  CHECK_NUMBER (timeout);
  CHECK_STRING (message);

  /* Set up the atimer.  */
  struct timespec interval = dtotimespec (XFLOATINT (timeout));
  struct atimer *timer = start_atimer (ATIMER_RELATIVE, interval,
				       with_delayed_message_display,
				       scm_to_utf8_string (message));
  dynwind_begin ();
  record_unwind_protect_ptr (with_delayed_message_cancel, timer);

  Lisp_Object result = calln (function);

  dynwind_end ();
  return result;
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

#define clobbered_eassert(E) static_assert (sizeof (E) != 0)

/* pop_handler, set_handlerlist, icc_thunk, icc_handler, restore_handler
   removed - catch/throw and condition-case now use Guile's exception system.  */

/* Guile-based condition handling structures and functions.
   These use scm_c_catch with 'elisp-condition key instead of
   the C handlerlist mechanism.  */

struct guile_condition_env
{
  enum { GCE_0, GCE_1, GCE_2, GCE_N } type;
  union
  {
    Lisp_Object (*fun0) (void);
    Lisp_Object (*fun1) (Lisp_Object);
    Lisp_Object (*fun2) (Lisp_Object, Lisp_Object);
    Lisp_Object (*funn) (ptrdiff_t, Lisp_Object *);
  };
  Lisp_Object arg1;
  Lisp_Object arg2;
  ptrdiff_t nargs;
  Lisp_Object *args;
  Lisp_Object handlers;  /* Conditions to catch (Qerror, Qt, or list) */
  Lisp_Object (*hfun) (Lisp_Object);  /* Handler function */
  Lisp_Object (*hfunn) (Lisp_Object, ptrdiff_t, Lisp_Object *);
};

/* Check if error matches the handler conditions.  */
static bool
error_matches_handlers (Lisp_Object error_symbol, Lisp_Object handlers)
{
  if (EQ (handlers, Qt))
    return true;
  if (EQ (handlers, Qerror))
    {
      Lisp_Object conditions = Fget (error_symbol, Qerror_conditions);
      return !NILP (Fmemq (Qerror, conditions));
    }
  if (CONSP (handlers))
    {
      Lisp_Object conditions = Fget (error_symbol, Qerror_conditions);
      for (Lisp_Object tail = handlers; CONSP (tail); tail = XCDR (tail))
        {
          if (!NILP (Fmemq (XCAR (tail), conditions)))
            return true;
        }
      return false;
    }
  /* Single symbol */
  Lisp_Object conditions = Fget (error_symbol, Qerror_conditions);
  return !NILP (Fmemq (handlers, conditions));
}

/* Body function for Guile-based condition case.  */
static SCM
guile_condition_body (void *data)
{
  struct guile_condition_env *e = data;
  Lisp_Object result;

  switch (e->type)
    {
    case GCE_0:
      result = e->fun0 ();
      break;
    case GCE_1:
      result = e->fun1 (e->arg1);
      break;
    case GCE_2:
      result = e->fun2 (e->arg1, e->arg2);
      break;
    case GCE_N:
      result = e->funn (e->nargs, e->args);
      break;
    default:
      emacs_abort ();
    }
  return result;
}

/* Handler function for Guile-based condition case.
   Checks if error matches handlers, calls hfun or re-throws.  */
static SCM
guile_condition_handler (void *data, SCM key, SCM args)
{
  struct guile_condition_env *e = data;

  /* args is (error-symbol . error-data) from scm_throw */
  Lisp_Object error_symbol = scm_is_pair (args) ? scm_car (args) : Qerror;
  Lisp_Object error_data = scm_is_pair (args) && scm_is_pair (scm_cdr (args))
    ? scm_cadr (args) : Qnil;
  Lisp_Object error = Fcons (error_symbol, error_data);

  /* Check if this handler should catch the error */
  if (error_matches_handlers (error_symbol, e->handlers))
    {
      /* Call the handler function */
      return e->hfun (error);
    }
  else
    {
      /* Re-throw for outer handler */
      scm_throw (key, args);
      /* scm_throw doesn't return */
      emacs_abort ();
    }
}

/* Handler variant for internal_condition_case_n that passes nargs/args.  */
static SCM
guile_condition_handler_n (void *data, SCM key, SCM args)
{
  struct guile_condition_env *e = data;

  Lisp_Object error_symbol = scm_is_pair (args) ? scm_car (args) : Qerror;
  Lisp_Object error_data = scm_is_pair (args) && scm_is_pair (scm_cdr (args))
    ? scm_cadr (args) : Qnil;
  Lisp_Object error = Fcons (error_symbol, error_data);

  if (error_matches_handlers (error_symbol, e->handlers))
    {
      return e->hfunn (error, e->nargs, e->args);
    }
  else
    {
      scm_throw (key, args);
      emacs_abort ();
    }
}

/* icc_handler_n, icc_lisp_handler removed - condition-case now uses Guile catch */

/* Set up a catch, then call C function FUNC on argument ARG.
   FUNC should return a Lisp_Object.
   This is how catches are done from within C code.

   Uses scm_c_catch with 'elisp-throw key instead of C handlerlist.  */

/* Environment for internal_catch using Guile catch */
struct internal_catch_env
{
  Lisp_Object tag;                        /* Expected catch tag */
  Lisp_Object (*func) (Lisp_Object);      /* Function to call */
  Lisp_Object arg;                        /* Argument to function */
};

/* Body function for scm_c_catch in internal_catch */
static SCM
internal_catch_body (void *data)
{
  struct internal_catch_env *env = data;
  /* No longer need to save/restore handlerlist - nothing pushes to it anymore */
  return env->func (env->arg);
}

/* Handler function for scm_c_catch in internal_catch.
   args is (thrown-tag value) from scm_throw.
   If thrown-tag matches our expected tag, return value.
   Otherwise re-throw to outer catch.  */
static SCM
internal_catch_handler (void *data, SCM key, SCM args)
{
  struct internal_catch_env *env = data;
  Lisp_Object thrown_tag = scm_car (args);
  Lisp_Object value = scm_cadr (args);

  if (EQ (thrown_tag, env->tag))
    return value;  /* Tag matches - return the caught value */
  else
    {
      /* Tag doesn't match - re-throw to outer catch */
      scm_throw (key, args);
      /* scm_throw doesn't return */
      emacs_abort ();
    }
}

Lisp_Object
internal_catch (Lisp_Object tag,
		Lisp_Object (*func) (Lisp_Object), Lisp_Object arg)
{
  struct internal_catch_env env = { .tag = tag, .func = func, .arg = arg };
  return scm_c_catch (elisp_throw_sym,
                      internal_catch_body, &env,
                      internal_catch_handler, &env,
                      NULL, NULL);
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

   This is used for correct unwinding in Fthrow and Fsignal.

   Bindings is handled by Guile's dynamic-wind --
   catch/throw uses Guile's scm_throw.  */

DEFUN ("throw", Fthrow, Sthrow, 2, 2, 0,
       doc: /* Throw to the catch for TAG and return VALUE from it.
Both TAG and VALUE are evalled.  */
       attributes: noreturn)
  (register Lisp_Object tag, Lisp_Object value)
{
  /* nil tag is always an error - no catch can match it */
  if (NILP (tag))
    xsignal2 (Qno_catch, tag, value);

  /* Throw to Guile's catch mechanism.
     The args are (tag value) - internal_catch_handler will check tag match.
     If no catch matches, scm_eval_error_handler will convert to no-catch.  */
  scm_throw (elisp_throw_sym, scm_list_2 (tag, value));

  /* scm_throw doesn't return. If we somehow get here, abort.  */
  emacs_abort ();
}

/* This C stub is superseded by the elisp implementation in boot.el once
   boot.el is loaded.  The elisp version uses Guile's with-exception-handler
   for proper handler-bind semantics.  This stub exists only for very early
   bootstrap before boot.el is loaded, and simply calls the body function.  */

DEFUN ("handler-bind-1", Fhandler_bind_1, Shandler_bind_1, 1, MANY, 0,
       doc: /* Set up error handlers around execution of BODYFUN.
BODYFUN should be a function and it is called with no arguments.
CONDITIONS should be a list of condition names (symbols).
When an error is signaled during execution of BODYFUN, if that
error matches one of CONDITIONS, then the associated HANDLER is
called with the error as argument.
HANDLER should either transfer the control via a non-local exit,
or return normally.
If it returns normally, the search for an error handler continues
from where it left off.

NOTE: This C function is a bootstrap stub.  Once boot.el is loaded,
the elisp implementation supersedes this and provides proper semantics.

usage: (handler-bind BODYFUN [CONDITIONS HANDLER]...)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  eassert (nargs >= 1);
  Lisp_Object bodyfun = args[0];
  if (nargs % 2 == 0)
    error ("Trailing CONDITIONS without HANDLER in `handler-bind`");
  /* Bootstrap stub: just call the body function, ignoring handlers.
     The elisp version in boot.el provides proper handler-bind semantics.  */
  return call0 (bodyfun);
}

/* ilcc1 and internal_lisp_condition_case removed - condition-case uses boot.el Guile catch */

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
  /* Use Guile's catch mechanism for condition handling.
     All errors are thrown to 'elisp-condition by signal_or_quit.  */
  struct guile_condition_env env = {
    .type = GCE_0,
    .fun0 = bfun,
    .handlers = handlers,
    .hfun = hfun
  };
  return scm_c_catch (elisp_condition_sym,
                      guile_condition_body, &env,
                      guile_condition_handler, &env,
                      NULL, NULL);
}

/* Like internal_condition_case but call BFUN with ARG as its argument.  */

Lisp_Object
internal_condition_case_1 (Lisp_Object (*bfun) (Lisp_Object), Lisp_Object arg,
			   Lisp_Object handlers,
			   Lisp_Object (*hfun) (Lisp_Object))
{
  struct guile_condition_env env = {
    .type = GCE_1,
    .fun1 = bfun,
    .arg1 = arg,
    .handlers = handlers,
    .hfun = hfun
  };
  return scm_c_catch (elisp_condition_sym,
                      guile_condition_body, &env,
                      guile_condition_handler, &env,
                      NULL, NULL);
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
  struct guile_condition_env env = {
    .type = GCE_2,
    .fun2 = bfun,
    .arg1 = arg1,
    .arg2 = arg2,
    .handlers = handlers,
    .hfun = hfun
  };
  return scm_c_catch (elisp_condition_sym,
                      guile_condition_body, &env,
                      guile_condition_handler, &env,
                      NULL, NULL);
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
  struct guile_condition_env env = {
    .type = GCE_N,
    .funn = bfun,
    .nargs = nargs,
    .args = args,
    .handlers = handlers,
    .hfunn = hfun
  };
  return scm_c_catch (elisp_condition_sym,
                      guile_condition_body, &env,
                      guile_condition_handler_n, &env,
                      NULL, NULL);
}

static Lisp_Object Qcatch_all_memory_full;

/* Like a combination of internal_condition_case_1 and internal_catch.
   Catches all signals and throws.  Never exits nonlocally; returns
   Qcatch_all_memory_full if no handler could be allocated.  */

Lisp_Object
internal_catch_all (Lisp_Object (*function) (void *), void *argument,
                    Lisp_Object (*handler) (enum nonlocal_exit, Lisp_Object))
{
  /* Simplified - now uses Guile catch mechanism */
  return internal_condition_case_1 (function, argument, Qnil, handler);
}

/* push_handler and push_handler_nosignal removed - uses Guile catch */

static Lisp_Object signal_or_quit (Lisp_Object, Lisp_Object, bool);
/* find_handler_clause removed - unused with Guile catch mechanism */
static bool maybe_call_debugger (Lisp_Object conditions, Lisp_Object error);

static void
process_quit_flag (void)
{
  Lisp_Object flag = Vquit_flag;
  Vquit_flag = Qnil;
  if (EQ (flag, Qkill_emacs))
    Fkill_emacs (Qnil, Qnil);
  if (EQ (Vthrow_on_input, flag))
    Fthrow (Vthrow_on_input, Qt);
  quit ();
}

void
probably_quit (void)
{
  if (!NILP (Vquit_flag) && NILP (Vinhibit_quit))
    process_quit_flag ();
  else if (pending_signals)
    process_pending_signals ();
}

DEFUN ("signal", Fsignal, Ssignal, 2, 2, 0,
       doc: /* Signal an error.  Args are ERROR-SYMBOL and associated DATA.
This function does not return.

When `noninteractive' is non-nil (in particular, in batch mode), an
unhandled error calls `kill-emacs', which terminates the Emacs
session with a non-zero exit code.

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
   If CONTINUABLE, the caller allows this function to return
   (presumably after calling the debugger);
   Otherwise this function is like Fsignal and does not return.  */

static Lisp_Object
signal_or_quit (Lisp_Object error_symbol, Lisp_Object data, bool continuable)
{
  /* When memory is full, ERROR-SYMBOL is nil,
     and DATA is (REAL-ERROR-SYMBOL . REAL-DATA).
     That is a special case--don't do this in other situations.  */
  bool oom = NILP (error_symbol);
  Lisp_Object error             /* The error object.  */
    = oom ? data
      : (!SYMBOLP (error_symbol) && NILP (data)) ? error_symbol
      : Fcons (error_symbol, data);
  Lisp_Object conditions;
  Lisp_Object real_error_symbol
    = CONSP (error) ? XCAR (error) : error_symbol;

  if (waiting_for_input)
    emacs_abort ();

  /* This hook is used by edebug.  */
  if (! NILP (Vsignal_hook_function)
      && !oom)
    {
      dynwind_begin ();
      max_ensure_room (20);
      call2 (Vsignal_hook_function, error_symbol, data);
      dynwind_end ();
    }

  conditions = Fget (real_error_symbol, Qerror_conditions);

  /* Check if debugger should be called.  */
  bool debugger_called = false;
  if (!oom && !NILP (Vdebug_on_signal))
    {
      debugger_called = maybe_call_debugger (conditions, error);
      if (continuable && debugger_called)
	return Qnil;
    }

  /* Always throw to Guile's 'elisp-condition.
     All condition handlers (including internal_condition_case) use
     scm_c_catch to catch this.  */
  scm_throw (elisp_condition_sym, scm_list_2 (error_symbol, data));

  /* scm_throw doesn't return. If we somehow get here, it's fatal.  */
  Lisp_Object string = Ferror_message_string (error);
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
   If ARG is not a proper list, make it a one-element list.  */

void
signal_error (const char *s, Lisp_Object arg)
{
  if (NILP (Fproper_list_p (arg)))
    arg = list1 (arg);

  xsignal (Qerror, Fcons (build_string (s), arg));
}

/* Simplified version of 'define-error' that works with pure
   objects.  */

void
define_error (Lisp_Object name, const char *message, Lisp_Object parent)
{
  eassert (SYMBOLP (name));
  eassert (SYMBOLP (parent));
  Lisp_Object parent_conditions = Fget (parent, Qerror_conditions);
  eassert (CONSP (parent_conditions));
  eassert (!NILP (Fmemq (parent, parent_conditions)));
  eassert (NILP (Fmemq (name, parent_conditions)));
  Fput (name, Qerror_conditions, pure_cons (name, parent_conditions));
  Fput (name, Qerror_message, build_pure_c_string (message));
}

/* Use this for arithmetic overflow, e.g., when an integer result is
   too large even for a bignum.  */
void
overflow_error (void)
{
  xsignal0 (Qoverflow_error);
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

/* Say whether SIGNAL is a `quit' error (or inherits from it).  */
bool
signal_quit_p (Lisp_Object error)
{
  Lisp_Object signal = CONSP (error) ? XCAR (error) : Qnil;
  Lisp_Object list;

  return EQ (signal, Qquit)
    || (SYMBOLP (signal)
	&& CONSP (list = Fget (signal, Qerror_conditions))
	&& !NILP (Fmemq (Qquit, list)));
}

/* Call the debugger if calling it is currently enabled for CONDITIONS.
   SIG and DATA describe the signal.  There are two ways to pass them:
    = SIG is the error symbol, and DATA is the rest of the data.
    = SIG is nil, and DATA is (SYMBOL . REST-OF-DATA).
      This is for memory-full errors only.  */
static bool
maybe_call_debugger (Lisp_Object conditions, Lisp_Object error)
{
  if (
      /* Don't try to run the debugger with interrupts blocked.
	 The editing loop would return anyway.  */
      ! input_blocked_p ()
      && NILP (Vinhibit_debugger)
      /* Does user want to enter debugger for this kind of error?  */
      && (signal_quit_p (error)
	  ? debug_on_quit
	  : wants_debugger (Vdebug_on_error, conditions))
      && ! skip_debugger (conditions, error)
      /* See commentary on definition of
         `internal-when-entered-debugger'.  */
      && when_entered_debugger < num_nonmacro_input_events)
    {
      call_debugger (list2 (Qerror, error));
      return 1;
    }

  return 0;
}

/* find_handler_clause removed - unused with Guile catch mechanism */

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
  bool genfun = false; /* If true, we should consult `interactive-form'.  */

  fun = function;

  fun = indirect_function (fun);
  if (NILP (fun))
    return Qnil;

  if (scm_is_true (scm_procedure_p (fun)))
    return (scm_is_pair (scm_assq (Qinteractive_form,
                                   scm_procedure_properties (fun)))
            ? Qt : Qnil);

#ifdef HAVE_MODULES
  /* Module functions are interactive if their `interactive_form'
     field is non-nil. */
  else if (MODULE_FUNCTIONP (fun))
    {
      if (!NILP (module_function_interactive_form (XMODULE_FUNCTION (fun))))
        return Qt;
    }
#endif

  /* Strings and vectors are keyboard macros.  */
  else if (STRINGP (fun) || VECTORP (fun))
    return (NILP (for_call_interactively) ? Qt : Qnil);

  /* Lists may represent commands.  */
  else if (!CONSP (fun))
    return Qnil;
  else
    {
      Lisp_Object funcar = XCAR (fun);
      if (EQ (funcar, Qautoload))
        {
          if (!NILP (Fcar (Fcdr (Fcdr (XCDR (fun))))))
            return Qt;
        }
      else
        {
          Lisp_Object body = CDR_SAFE (XCDR (fun));
          if (!EQ (funcar, Qlambda))
	    return Qnil;
	  if (!NILP (Fassq (Qinteractive, body)))
	    return Qt;
	  else
	    return Qnil;
	}
    }

  /* By now, if it's not a function we already returned nil.  */

  /* Check an `interactive-form' property if present, analogous to the
     function-documentation property.  */
  fun = function;
  while (SYMBOLP (fun))
    {
      Lisp_Object tmp = Fget (fun, Qinteractive_form);
      if (!NILP (tmp))
	error ("Found an 'interactive-form' property!");
      fun = Fsymbol_function (fun);
    }

  /* If there's no immediate interactive form but it's an OClosure,
     then delegate to the generic-function in case it has
     a type-specific interactive-form.  */
  if (genfun)
    {
      Lisp_Object iform = call1 (Qinteractive_form, fun);
      return NILP (iform) ? Qnil : Qt;
    }
  else
    return Qnil;
}

DEFUN ("autoload", Fautoload, Sautoload, 2, 5, 0,
       doc: /* Define FUNCTION to autoload from FILE.
FUNCTION is a symbol; FILE is a file name string to pass to `load'.

Third arg DOCSTRING is documentation for the function.

Fourth arg INTERACTIVE if non-nil says function can be called
interactively.  If INTERACTIVE is a list, it is interpreted as a list
of modes the function is applicable for.

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

static void
un_autoload (Lisp_Object oldqueue)
{
  /* Queue to unwind is current value of Vautoload_queue.
     oldqueue is the shadowed value to leave in Vautoload_queue.  */
  Lisp_Object queue = Vautoload_queue;
  Vautoload_queue = oldqueue;
  while (CONSP (queue))
    {
      Lisp_Object first = XCAR (queue);
      if (CONSP (first) && BASE_EQ (XCAR (first), make_fixnum (0)))
	Vfeatures = XCDR (first);
      else
	Ffset (first, Fcar (Fcdr (Fget (first, Qfunction_history))));
      queue = XCDR (queue);
    }
}

Lisp_Object
load_with_autoload_queue
  (Lisp_Object file, Lisp_Object noerror, Lisp_Object nomessage,
   Lisp_Object nosuffix, Lisp_Object must_suffix)
{
  dynwind_begin ();

  /* If autoloading gets an error (which includes the error of failing
     to define the function being called), we use Vautoload_queue
     to undo function definitions and `provide' calls made by
     the function.  We do this in the specific case of autoloading
     because autoloading is not an explicit request "load this file",
     but rather a request to "call this function".

     The value saved here is to be restored into Vautoload_queue.  */
  record_unwind_protect (un_autoload, Vautoload_queue);
  Vautoload_queue = Qt;
  Lisp_Object tem
    = save_match_data_load (file, noerror, nomessage, nosuffix, must_suffix);

  /* Once loading finishes, don't undo it.  */
  Vautoload_queue = Qt;
  dynwind_end ();
  return tem;
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
  /* Delegate to Scheme implementation in (emacs loader).
     The Scheme version handles circular autoload detection via *files-being-loaded*.  */
  SCM scm_func = scm_c_private_ref ("emacs loader",
                                    "elisp-autoload-do-load");
  return SCM_CALL_3 (scm_func, fundef, funname, macro_only);
}


static Lisp_Object list_of_t;  /* Never-modified constant containing (t).  */

DEFUN ("eval", Feval, Seval, 1, 2, 0,
       doc: /* Evaluate FORM and return its value.
If LEXICAL is `t', evaluate using lexical binding by default.
This is the recommended value.

If absent or `nil', use dynamic scoping only.

LEXICAL can also represent an actual lexical environment; see the Info
node `(elisp)Eval' for details.  */)
  (Lisp_Object form, Lisp_Object lexical)
{
  dynwind_begin ();
  specbind_guile (Qinternal_interpreter_environment,
	    CONSP (lexical) || NILP (lexical) ? lexical : list_of_t);
  Lisp_Object tem = eval_sub (form);
  dynwind_end ();
  return tem;
}

/* Structure for passing eval arguments to scm_c_catch */
struct scm_eval_data
{
  Lisp_Object form;
};

/* Body function for scm_c_catch - calls the Scheme eval */
static SCM
scm_eval_body (void *data)
{
  struct scm_eval_data *edata = (struct scm_eval_data *) data;
  return SCM_CALL_1 (eval_fn, edata->form);
}

/* Error handler for Guile exceptions during eval.
   This converts Guile exceptions to elisp signals by throwing directly
   to 'elisp-condition.  We can't use xsignal here because throwing from
   inside a handler goes to the OUTER catch, bypassing elisp condition-case.  */
static SCM
scm_eval_error_handler (void *data, SCM key, SCM args)
{
  struct scm_eval_data *edata = (struct scm_eval_data *) data;

  /* If this is an elisp condition, re-throw it directly.  */
  if (scm_is_eq (key, elisp_condition_sym))
    {
      scm_throw (key, args);
      /* scm_throw doesn't return */
    }

  /* If this is an elisp throw, re-throw it to propagate to outer catch.  */
  if (scm_is_eq (key, elisp_throw_sym))
    {
      scm_throw (key, args);
      /* scm_throw doesn't return */
    }

  /* Handle wrong-number-of-arguments error - convert and throw as elisp-condition */
  if (scm_is_eq (key, scm_from_latin1_symbol ("wrong-number-of-args")))
    {
      /* Extract function name from args if possible */
      SCM proc = SCM_BOOL_F;
      Lisp_Object fun_name = Qnil;
      if (scm_is_pair (args) && scm_is_pair (scm_cdr (args)))
        {
          SCM arg_list = scm_car (scm_cdr (scm_cdr (args)));
          if (scm_is_pair (arg_list))
            proc = scm_car (arg_list);
        }

      if (scm_is_true (scm_procedure_p (proc)))
        {
          SCM proc_name = scm_procedure_name (proc);
          if (scm_is_symbol (proc_name))
            fun_name = proc_name;
        }

      if (NILP (fun_name))
        fun_name = build_string ("unknown");

      /* Throw directly to elisp-condition instead of using xsignal */
      scm_throw (elisp_condition_sym,
                 scm_list_2 (Qwrong_number_of_arguments,
                             list2 (fun_name, make_fixnum (0))));
    }
  /* Handle other Guile exceptions */
  else
    {
      /* Build error message from Guile exception */
      SCM msg = SCM_CALL_1 (scm_c_public_ref ("guile", "object->string"), args);
      char *error_msg = scm_to_utf8_string (msg);
      char *key_str = scm_to_utf8_string (scm_symbol_to_string (key));

      /* Create combined error message */
      char combined_msg[512];
      snprintf (combined_msg, sizeof (combined_msg), "%s: %s", key_str, error_msg);

      free (error_msg);
      free (key_str);

      /* Throw directly to elisp-condition instead of using xsignal */
      scm_throw (elisp_condition_sym,
                 scm_list_2 (Qerror, list1 (build_string (combined_msg))));
    }

  /* Should never reach here */
  return SCM_UNDEFINED;
}

/* Eval a sub-expression of the current expression (i.e. in the same
   lexical scope).  */
static Lisp_Object
eval_sub_1 (Lisp_Object form)
{
  maybe_quit ();

  /* Wrap SCM_CALL_1 with exception handling to catch Guile exceptions
     and convert them to Elisp signals */
  struct scm_eval_data edata;
  edata.form = form;

  return scm_c_catch (SCM_BOOL_T,
                      scm_eval_body, &edata,
                      scm_eval_error_handler, &edata,
                      NULL, NULL);
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
  ptrdiff_t i, funcall_nargs;
  Lisp_Object *funcall_args = NULL;
  Lisp_Object spread_arg = args[nargs - 1];
  Lisp_Object fun = args[0];
  USE_SAFE_ALLOCA;

  ptrdiff_t numargs = list_length (spread_arg);

  if (numargs == 0)
    return Ffuncall (max (1, nargs - 1), args);
  else if (numargs == 1)
    {
      args [nargs - 1] = XCAR (spread_arg);
      return Ffuncall (nargs, args);
    }

  numargs += nargs - 2;

  /* Optimize for no indirection.  */
  if (SYMBOLP (fun) && !NILP (fun)
      && (fun = SYMBOL_FUNCTION (fun), SYMBOLP (fun)))
    {
      fun = indirect_function (fun);
      if (NILP (fun))
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

  Lisp_Object retval = Ffuncall (funcall_nargs, funcall_args);

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

  if (BASE_EQ (val, Qunbound) || NILP (val))
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
  return NILP (arg) ? calln (fn) : CALLN (Fapply, fn, arg);
}

DEFUN ("functionp", Ffunctionp, Sfunctionp, 1, 1, 0,
       doc: /* Return t if OBJECT is a function.

An object is a function if it is callable via `funcall'; this includes
symbols with function bindings, but excludes macros and special forms.

Ordinarily return nil if OBJECT is not a function, although t might be
returned in rare cases.  */)
     (Lisp_Object object)
{
  if (FUNCTIONP (object))
    return Qt;
  return Qnil;
}

bool
FUNCTIONP (Lisp_Object object)
{
  if (SYMBOLP (object) && !NILP (Ffboundp (object)))
    {
      object = Findirect_function (object, Qt);

      if (CONSP (object) && EQ (XCAR (object), Qautoload))
	{
	  /* Autoloaded symbols are functions, except if they load
	     macros or keymaps.  */
	  for (int i = 0; i < 4 && CONSP (object); i++)
	    object = XCDR (object);

	  return ! (CONSP (object) && !NILP (XCAR (object)));
	}
    }

  if (scm_is_true (scm_procedure_p (object)))
    return 1;
  else if (MODULE_FUNCTIONP (object))
    return true;
  else if (CONSP (object))
    {
      Lisp_Object car = XCAR (object);
      return EQ (car, Qlambda);
    }
  else
    return false;
}

/* Structure for passing funcall arguments to scm_c_catch */
struct scm_funcall_data
{
  SCM fun;
  Lisp_Object *args;
  ptrdiff_t numargs;
  Lisp_Object original_fun;
};

/* Body function for scm_c_catch - calls the Scheme procedure */
static SCM
scm_funcall_body (void *data)
{
  struct scm_funcall_data *fdata = (struct scm_funcall_data *) data;
  return SCM_CALL_N (fdata->fun, fdata->args + 1, fdata->numargs);
}

/* Error handler for Guile exceptions during funcall.
   Converts Guile exceptions to elisp signals by throwing directly.  */
static SCM
scm_funcall_error_handler (void *data, SCM key, SCM args)
{
  struct scm_funcall_data *fdata = (struct scm_funcall_data *) data;

  /* If this is an elisp condition, re-throw it directly.  */
  if (scm_is_eq (key, elisp_condition_sym))
    {
      scm_throw (key, args);
      /* scm_throw doesn't return */
    }

  /* If this is an uncaught elisp throw, convert to no-catch error.  */
  if (scm_is_eq (key, elisp_throw_sym))
    {
      /* args is (tag value) */
      Lisp_Object thrown_tag = scm_car (args);
      Lisp_Object thrown_value = scm_cadr (args);
      /* Convert to elisp no-catch error */
      scm_throw (elisp_condition_sym,
                 scm_list_2 (Qno_catch, list2 (thrown_tag, thrown_value)));
      /* scm_throw doesn't return */
    }

  /* Handle wrong-number-of-arguments error */
  if (scm_is_eq (key, scm_from_latin1_symbol ("wrong-number-of-args")))
    {
      /* Throw directly to elisp-condition */
      scm_throw (elisp_condition_sym,
                 scm_list_2 (Qwrong_number_of_arguments,
                             list2 (fdata->original_fun,
                                    make_fixnum (fdata->numargs))));
    }
  /* Handle other Guile exceptions by converting to generic Elisp error */
  else
    {
      /* Build error message from Guile exception */
      SCM msg = SCM_CALL_1 (scm_c_public_ref ("guile", "object->string"), args);
      char *error_msg = scm_to_utf8_string (msg);
      char *key_str = scm_to_utf8_string (scm_symbol_to_string (key));

      /* Create error message combining key and args */
      char combined_msg[512];
      snprintf (combined_msg, sizeof (combined_msg), "%s: %s", key_str, error_msg);

      free (error_msg);
      free (key_str);

      /* Throw directly to elisp-condition */
      scm_throw (elisp_condition_sym,
                 scm_list_2 (Qerror, list1 (build_string (combined_msg))));
    }

  /* Should never reach here, but return SCM_UNDEFINED for safety */
  return SCM_UNDEFINED;
}

Lisp_Object
funcall_general (Lisp_Object fun, ptrdiff_t numargs, Lisp_Object *args)
{
  Lisp_Object original_fun = fun;
 retry:
  if (SYMBOLP (fun) && !NILP (fun)
      && (fun = SYMBOL_FUNCTION (fun), SYMBOLP (fun)))
    fun = indirect_function (fun);

  if (scm_is_true (scm_procedure_p (fun)))
    {
      /* Wrap SCM_CALL_n with exception handling to catch Guile exceptions
         and convert them to Elisp signals that condition-case can catch */
      struct scm_funcall_data fdata;
      fdata.fun = fun;
      fdata.args = args;
      fdata.numargs = numargs;
      fdata.original_fun = original_fun;

      return scm_c_catch (SCM_BOOL_T,
                          scm_funcall_body, &fdata,
                          scm_funcall_error_handler, &fdata,
                          NULL, NULL);
    }

  else if (NATIVE_COMP_FUNCTION_DYNP (fun)
	   || MODULE_FUNCTIONP (fun))
    return funcall_lambda (fun, numargs, args);
  else
    {
      if (NILP (fun))
	{
	  fprintf (stderr, "DEBUG funcall_general: void-function signal for %s\n",
		   SDATA (SYMBOL_NAME (original_fun)));
	  xsignal1 (Qvoid_function, original_fun);
	}
      if (!CONSP (fun))
	xsignal1 (Qinvalid_function, original_fun);
      Lisp_Object funcar = XCAR (fun);
      if (!SYMBOLP (funcar))
	xsignal1 (Qinvalid_function, original_fun);
      if (EQ (funcar, Qlambda))
	return funcall_lambda (fun, numargs, args);
      else if (EQ (funcar, Qautoload))
	{
	  fprintf (stderr, "DEBUG funcall_general: before autoload-do-load for %s\n",
		   SDATA (SYMBOL_NAME (original_fun)));
	  Fautoload_do_load (fun, original_fun, Qnil);
	  fprintf (stderr, "DEBUG funcall_general: after autoload-do-load, fun now = %s\n",
		   NILP (SYMBOL_FUNCTION (original_fun)) ? "nil" : "non-nil");
	  fun = original_fun;
	  goto retry;
	}
      else
	xsignal1 (Qinvalid_function, original_fun);
    }
}

static Lisp_Object
Ffuncall1 (ptrdiff_t nargs, Lisp_Object *args)
{
  return SCM_CALL_N (funcall_fn, args, nargs);
}

Lisp_Object
Ffuncall (ptrdiff_t nargs, Lisp_Object *args)
{
  return scm_c_value_ref (Ffuncall1 (nargs, args), 0);
}


static Lisp_Object
safe_eval_handler (Lisp_Object arg, ptrdiff_t nargs, Lisp_Object *args)
{
  add_to_log ("Error muted by safe_call: %S signaled %S",
	      Flist (nargs, args), arg);
  return Qnil;
}

Lisp_Object
safe_funcall (ptrdiff_t nargs, Lisp_Object *args)
{
  dynwind_begin ();
  /* FIXME: This function started its life in 'xdisp.c' for use internally
     by the redisplay.  So it was important to inhibit redisplay.
     Not clear if we still need this 'specbind' now that 'xdisp.c' has its
     own version of this code.  */
  specbind_guile (Qinhibit_redisplay, Qt);
  /* Use Qt to ensure debugger does not run.  */
  Lisp_Object val = internal_condition_case_n (Ffuncall, nargs, args, Qt,
				               safe_eval_handler);
  dynwind_end ();
  return val;
}

Lisp_Object
safe_eval (Lisp_Object sexp)
{
  return safe_calln (Qeval, sexp, Qt);
}

#if 0
/* Apply a C subroutine SUBR to the NUMARGS evaluated arguments in ARG_VECTOR
   and return the result of evaluation.  */

Lisp_Object
funcall_subr (struct Lisp_Subr *subr, ptrdiff_t numargs, Lisp_Object *args)
{
  eassume (numargs >= 0);
  if (numargs >= subr->min_args)
    {
      /* Conforming call to finite-arity subr.  */
      ptrdiff_t maxargs = subr->max_args;
      if (numargs <= maxargs && maxargs <= 8)
	{
	  Lisp_Object argbuf[8];
	  Lisp_Object *a;
	  if (numargs < maxargs)
	    {
	      eassume (maxargs <= ARRAYELTS (argbuf));
	      a = argbuf;
	      memcpy (a, args, numargs * word_size);
	      memclear (a + numargs, (maxargs - numargs) * word_size);
	    }
	  else
	    a = args;
	  switch (maxargs)
	    {
	    case 0:
	      return subr->function.a0 ();
	    case 1:
	      return subr->function.a1 (a[0]);
	    case 2:
	      return subr->function.a2 (a[0], a[1]);
	    case 3:
	      return subr->function.a3 (a[0], a[1], a[2]);
	    case 4:
	      return subr->function.a4 (a[0], a[1], a[2], a[3]);
	    case 5:
	      return subr->function.a5 (a[0], a[1], a[2], a[3], a[4]);
	    case 6:
	      return subr->function.a6 (a[0], a[1], a[2], a[3], a[4], a[5]);
	    case 7:
	      return subr->function.a7 (a[0], a[1], a[2], a[3], a[4], a[5],
					a[6]);
	    case 8:
	      return subr->function.a8 (a[0], a[1], a[2], a[3], a[4], a[5],
					a[6], a[7]);
	    }
	  eassume (false);	/* In case the compiler is too stupid.  */
	}

      /* Call to n-adic subr.  */
      if (maxargs == MANY || maxargs > 8)
	return subr->function.aMANY (numargs, args);
    }

  /* Anything else is an error.  */
  Lisp_Object fun;
  XSETSUBR (fun, subr);
  if (subr->max_args == UNEVALLED)
    xsignal1 (Qinvalid_function, fun);
  else
    xsignal2 (Qwrong_number_of_arguments, fun, make_fixnum (numargs));
}
#endif

/* Apply a Lisp function FUN to the NARGS evaluated arguments in ARG_VECTOR
   and return the result of evaluation.
   FUN must be either a lambda-expression, a compiled-code object,
   or a module function.  */

static Lisp_Object
funcall_lambda (Lisp_Object fun, ptrdiff_t nargs, Lisp_Object *arg_vector)
{
  Lisp_Object syms_left, lexenv;

  if (CONSP (fun))
    {
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

  ptrdiff_t i = 0;
  bool optional = false;
  bool rest = false;
  bool previous_rest = false;
  dynwind_begin ();
  for (; CONSP (syms_left); syms_left = XCDR (syms_left))
    {
      maybe_quit ();

      Lisp_Object next = XCAR (syms_left);
      if (!BARE_SYMBOL_P (next))
	xsignal1 (Qinvalid_function, fun);

      if (BASE_EQ (next, Qand_rest))
        {
          if (rest || previous_rest)
            xsignal1 (Qinvalid_function, fun);
          rest = 1;
	  previous_rest = true;
        }
      else if (BASE_EQ (next, Qand_optional))
        {
          if (optional || rest || previous_rest)
            xsignal1 (Qinvalid_function, fun);
          optional = 1;
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
	    xsignal2 (Qwrong_number_of_arguments, fun, make_fixnum (nargs));
	  else
	    arg = Qnil;

	  /* Bind the argument.  */
	  if (!NILP (lexenv))
	    /* Lexically bind NEXT by adding it to the lexenv alist.  */
	    lexenv = Fcons (Fcons (next, arg), lexenv);
	  else
	    /* Dynamically bind NEXT.  */
	    specbind_guile (next, arg);
	  previous_rest = false;
	}
    }

  if (!NILP (syms_left) || previous_rest)
    xsignal1 (Qinvalid_function, fun);
  else if (i < nargs)
    xsignal2 (Qwrong_number_of_arguments, fun, make_fixnum (nargs));

  if (!BASE_EQ (lexenv, Vinternal_interpreter_environment))
    /* Instantiate a new lexical environment.  */
    specbind_guile (Qinternal_interpreter_environment, lexenv);

  Lisp_Object val = Fprogn (XCDR (XCDR (fun)));
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
      function = SYMBOL_FUNCTION (function);
      if (SYMBOLP (function))
	function = indirect_function (function);
    }

  if (CONSP (function) && EQ (XCAR (function), Qmacro))
    function = XCDR (function);

#ifdef HAVE_MODULES
  else if (MODULE_FUNCTIONP (function))
    result = module_function_arity (XMODULE_FUNCTION (function));
#endif
  else if (scm_is_true (scm_procedure_p (function)))
    {
      /* Handle Guile procedures */
      Lisp_Object arity = scm_procedure_minimum_arity (function);
      if (scm_is_false (arity))
	xsignal1 (Qinvalid_function, original);
      Lisp_Object min = XCAR (arity);
      Lisp_Object max;
      /* arity is (required optional rest) */
      if (scm_is_true (XCAR (XCDR (XCDR (arity)))))
	max = Qmany;
      else
	max = scm_sum (min, XCAR (XCDR (arity)));
      result = Fcons (min, max);
    }
  else
    {
      if (NILP (function))
	xsignal1 (Qvoid_function, original);
      if (!CONSP (function))
	xsignal1 (Qinvalid_function, original);
      funcar = XCAR (function);
      if (!SYMBOLP (funcar))
	xsignal1 (Qinvalid_function, original);
      if (EQ (funcar, Qlambda))
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
      syms_left = XCDR (fun);
      if (CONSP (syms_left))
	syms_left = XCAR (syms_left);
      else
	xsignal1 (Qinvalid_function, fun);
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
	return Fcons (make_fixnum (minargs), Qmany);
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

  return Fcons (make_fixnum (minargs), make_fixnum (maxargs));
}


/* Return true if SYMBOL's default currently has a let-binding
   which was made in the buffer that is now current.  */

bool
let_shadows_buffer_binding_p (sym_t symbol)
{
  /* Use Scheme binding registry for introspection.  */
  if (scm_is_false (let_shadows_buffer_binding_fn))
    let_shadows_buffer_binding_fn = scm_c_public_ref ("emacs bindings", "let-shadows-buffer-binding?");
  Lisp_Object buf = Fcurrent_buffer ();
  return !scm_is_false (scm_call_2 (let_shadows_buffer_binding_fn, symbol, buf));
}

/* specbind_guile: Dynamic binding using Guile's dynamic-wind.
   Binding stack is managed in Scheme (emacs bindings).
   Uses a Lisp vector to store binding data for the Guile unwinder.

   Binding data vector layout:
     [0] = kind (fixnum: 0=LET, 1=LET_LOCAL, 2=LET_DEFAULT)
     [1] = symbol
     [2] = old_value
     [3] = where (buffer for LET_LOCAL, nil otherwise)
*/

#define BINDING_KIND_LET         0
#define BINDING_KIND_LET_LOCAL   1
#define BINDING_KIND_LET_DEFAULT 2

static void
unbind_guile (void *data)
{
  Lisp_Object binding = (Lisp_Object) data;
  eassert (VECTORP (binding) && ASIZE (binding) == 4);

  EMACS_INT kind = XFIXNUM (AREF (binding, 0));
  Lisp_Object symbol = AREF (binding, 1);
  Lisp_Object where = AREF (binding, 3);

  /* Pop from Scheme binding registry and read old_value from it.
     This allows set-default-toplevel-value to modify the restored value.
     Registry entry format: #(symbol old-value kind where)  */
  if (scm_is_false (pop_binding_fn))
    pop_binding_fn = scm_c_public_ref ("emacs bindings", "pop-binding!");
  SCM entry = scm_call_0 (pop_binding_fn);

  /* Use old_value from registry entry, fall back to captured value.  */
  Lisp_Object old_value;
  if (scm_is_true (entry) && scm_is_vector (entry))
    old_value = scm_c_vector_ref (entry, 1);
  else
    old_value = AREF (binding, 2);

  switch (kind)
    {
    case BINDING_KIND_LET:
      {
        /* If variable has a trivial value (no forwarding), we can
           just set it.  But check if it changed to LOCALIZED during
           the binding (via make-local-variable).  */
        sym_t sym = XSYMBOL (symbol);
        if (SYMBOL_REDIRECT (sym) == SYMBOL_PLAINVAL)
          {
            SET_SYMBOL_VAL (sym, old_value);
            break;
          }
        /* FALLTHROUGH: variable became localized during binding */
      }
    case BINDING_KIND_LET_DEFAULT:
      Fset_default (symbol, old_value);
      break;

    case BINDING_KIND_LET_LOCAL:
      {
        eassert (BUFFERP (where));
        /* If this was a local binding, reset the value in the appropriate
           buffer, but only if that buffer's binding still exists.  */
        if (!NILP (Flocal_variable_p (symbol, where)))
          set_internal (symbol, old_value, where, SET_INTERNAL_UNBIND);
      }
      break;
    }
}

void
specbind_guile (Lisp_Object symbol, Lisp_Object value)
{
  /* Resolve aliases.  */
  sym_t sym = XBARE_SYMBOL (symbol);
  while (SYMBOL_REDIRECT (sym) == SYMBOL_VARALIAS)
    {
      sym = SYMBOL_ALIAS (sym);
      XSETSYMBOL (symbol, sym);
    }

  /* Create binding data vector: [kind, symbol, old_value, where] */
  Lisp_Object binding = make_vector (4, Qnil);
  EMACS_INT kind;
  Lisp_Object old_value;
  Lisp_Object where = Qnil;

  switch (SYMBOL_REDIRECT (sym))
    {
    case SYMBOL_PLAINVAL:
      /* The most common case: non-constant symbol with trivial value.  */
      kind = BINDING_KIND_LET;
      old_value = SYMBOL_VAL (sym);
      break;

    case SYMBOL_LOCALIZED:
    case SYMBOL_FORWARDED:
      {
        old_value = find_symbol_value (symbol);
        kind = BINDING_KIND_LET_LOCAL;
        where = Fcurrent_buffer ();

        if (SYMBOL_REDIRECT (sym) == SYMBOL_LOCALIZED)
          {
            if (!blv_found (SYMBOL_BLV (sym)))
              kind = BINDING_KIND_LET_DEFAULT;
          }
        else if (BUFFER_OBJFWDP (SYMBOL_FWD (sym)))
          {
            /* Per-buffer variable without local value: bind the default.  */
            if (NILP (Flocal_variable_p (symbol, Qnil)))
              kind = BINDING_KIND_LET_DEFAULT;
          }
        else if (KBOARD_OBJFWDP (SYMBOL_FWD (sym)))
          {
            /* KBOARD-forwarded: treat as plain LET.  */
            kind = BINDING_KIND_LET;
          }
        else
          kind = BINDING_KIND_LET;
        break;
      }

    default:
      emacs_abort ();
    }

  /* Store binding data.  */
  ASET (binding, 0, make_fixnum (kind));
  ASET (binding, 1, symbol);
  ASET (binding, 2, old_value);
  ASET (binding, 3, where);

  /* Write to Scheme binding registry (Phase 4: specpdl writes removed).  */
  if (scm_is_false (push_binding_fn))
    push_binding_fn = scm_c_public_ref ("emacs bindings", "push-binding!");
  scm_call_4 (push_binding_fn, symbol, old_value, scm_from_int (kind), where);

  /* Set the new value.  */
  switch (kind)
    {
    case BINDING_KIND_LET:
      if (SYMBOL_REDIRECT (sym) == SYMBOL_PLAINVAL && !SYMBOL_TRAPPED (sym))
        SET_SYMBOL_VAL (sym, value);
      else
        set_internal (symbol, value, Qnil, SET_INTERNAL_BIND);
      break;

    case BINDING_KIND_LET_DEFAULT:
      set_default_internal (symbol, value, SET_INTERNAL_BIND, NULL);
      break;

    case BINDING_KIND_LET_LOCAL:
      set_internal (symbol, value, Qnil, SET_INTERNAL_BIND);
      break;
    }

  /* Register unwind handler with Guile.  The binding vector will be
     GC-protected because it's passed to Guile.  */
  scm_dynwind_unwind_handler (unbind_guile, (void *) binding,
                              SCM_F_WIND_EXPLICITLY);
}

/* Phase 4: specpdl-track-binding and specpdl-untrack-binding removed.
   Scheme binding registry (emacs bindings) is now the sole source of truth
   for introspection functions like default-toplevel-value.  */

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
record_unwind_protect_intmax (void (*function) (intmax_t), intmax_t arg)
{
  record_unwind_protect_ptr_1 (function, arg, true);
}

void
record_unwind_protect_excursion (void)
{
  record_unwind_protect (save_excursion_restore, save_excursion_save ());
}

void
record_unwind_protect_void (void (*function) (void))
{
  record_unwind_protect_void_1 (function, true);
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

  return SCM_CALL_3 (scm_variable_ref (var), tag, thunk, handler);
}

SCM
make_prompt_tag (void)
{
  static SCM var = SCM_UNDEFINED;
  if (SCM_UNBNDP (var))
    var = scm_c_public_lookup ("guile", "make-prompt-tag");

  return SCM_CALL_0 (scm_variable_ref (var));
}

DEFUN ("debug-guile-cross-count", Fdebug_guile_cross_count,
       Sdebug_guile_cross_count, 0, 0, 0,
       doc: /* Return boundary crossing counts as (SCHEME-TO-C . C-TO-SCHEME).
These count the number of times execution has crossed between Scheme and C.  */)
  (void)
{
  return Fcons (make_int ((intmax_t) scheme_to_c_crossings),
                make_int ((intmax_t) c_to_scheme_crossings));
}

DEFUN ("debug-reset-guile-cross-count", Fdebug_reset_guile_cross_count,
       Sdebug_reset_guile_cross_count, 0, 0, 0,
       doc: /* Reset boundary crossing counters to zero.  */)
  (void)
{
  scheme_to_c_crossings = 0;
  c_to_scheme_crossings = 0;
  return Qnil;
}

void
syms_of_eval (void)
{
#include "eval.x"

  /* Initialize the Guile symbol for condition handling.  */
  elisp_condition_sym = scm_from_utf8_symbol ("elisp-condition");
  scm_gc_protect_object (elisp_condition_sym);

  DEFVAR_INT ("max-lisp-eval-depth", max_lisp_eval_depth,
	      doc: /* Limit on depth in `eval', `apply' and `funcall' before error.

This limit serves to catch infinite recursions for you before they cause
actual stack overflow in C, which would be fatal for Emacs.
You can safely make it considerably larger than its default value,
if that proves inconveniently small.  However, if you increase it too far,
Emacs could overflow the real C stack, and crash.  */);
  max_lisp_eval_depth = 10000;

  DEFVAR_INT ("lisp-eval-depth-reserve", lisp_eval_depth_reserve,
	      doc: /* Extra depth that can be allocated to handle errors.
This is the max depth that the system will add to `max-lisp-eval-depth'
when calling debuggers or `handler-bind' handlers.  */);
  lisp_eval_depth_reserve = 200;

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
  DEFSYM (QCdocumentation, ":documentation");
  DEFSYM (Qdebug, "debug");
  DEFSYM (Qdebug_early, "debug-early");
  DEFSYM (Qdebug_early__handler, "debug-early--handler");
  DEFSYM (Qdebugger_may_continue, "debugger-may-continue");
  DEFSYM (Qdisplay_warning, "display-warning");
  DEFSYM (Qlosing_value, "losing-value");

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
If you invoke Emacs with --debug-init, and want to remove some
elements from the default value of this variable, use `setq' to
change the value of the variable to a new list, rather than `delq'
to remove some errors from the list.
This overrides the variable `debug-on-error'.
It does not apply to errors handled by `condition-case'.  */);
  Vdebug_ignored_errors = Qnil;

  DEFVAR_BOOL ("debug-on-quit", debug_on_quit,
    doc: /* Non-nil means enter debugger if quit is signaled (C-g, for example).
Does not apply if quit is handled by a `condition-case'.  */);
  debug_on_quit = 0;

  DEFVAR_BOOL ("debug-on-next-call", debug_on_next_call,
	       doc: /* Non-nil means enter debugger before next `eval', `apply' or `funcall'.  */);

  DEFVAR_BOOL ("backtrace-on-redisplay-error", backtrace_on_redisplay_error,
	       doc: /* Non-nil means create a backtrace if a lisp error occurs in redisplay.
The backtrace is written to buffer *Redisplay-trace*.  */);
  backtrace_on_redisplay_error = false;

  DEFVAR_BOOL ("debugger-may-continue", debugger_may_continue,
	       doc: /* Non-nil means debugger may continue execution.
This is nil when the debugger is called under circumstances where it
might not be safe to continue.  */);
  debugger_may_continue = 1;

  DEFVAR_BOOL ("debugger-stack-frame-as-list", debugger_stack_frame_as_list,
	       doc: /* Non-nil means display call stack frames as lists. */);
  debugger_stack_frame_as_list = 0;

  DEFSYM (Qdebugger, "debugger");
  DEFVAR_LISP ("debugger", Vdebugger,
	       doc: /* Function to call to invoke debugger.
If due to frame exit, arguments are `exit' and the value being returned;
 this function's value will be returned instead of that.
If due to error, arguments are `error' and a list of arguments to `signal'.
If due to `apply' or `funcall' entry, one argument, `lambda'.
If due to `eval' entry, one argument, t.
IF the desired entry point of the debugger is higher in the call stack,
it can be specified with the keyword argument `:backtrace-base', whose
format should be the same as the BASE argument of `backtrace-frame'.  */);
  Vdebugger = Qdebug_early;

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

  DEFVAR_BOOL ("backtrace-on-error-noninteractive",
               backtrace_on_error_noninteractive,
               doc: /* Non-nil means print backtrace on error in batch mode.
If this is nil, errors in batch mode will just print the error
message upon encountering an unhandled error, without showing
the Lisp backtrace.  */);
  backtrace_on_error_noninteractive = true;

  /* The value of num_nonmacro_input_events as of the last time we
   started to enter the debugger.  If we decide to enter the debugger
   again when this is still equal to num_nonmacro_input_events, then we
   know that the debugger itself has an error, and we should just
   signal the error instead of entering an infinite loop of debugger
   invocations.  */
  DEFSYM (Qinternal_when_entered_debugger, "internal-when-entered-debugger");
  DEFVAR_INT ("internal-when-entered-debugger", when_entered_debugger,
              doc: /* The number of keyboard events as of last time `debugger' was called.
Used to avoid infinite loops if the debugger itself has an error.
Don't set this unless you're sure that can't happen.  */);

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

  DEFVAR_LISP ("internal-make-interpreted-closure-function",
	       Vinternal_make_interpreted_closure_function,
	       doc: /* Function to filter the env when constructing a closure.  */);
  Vinternal_make_interpreted_closure_function = Qnil;

  Vrun_hooks = intern_c_string ("run-hooks");
  staticpro (&Vrun_hooks);

  staticpro (&Vautoload_queue);
  Vautoload_queue = Qnil;
  staticpro (&Vsignaling_function);
  Vsignaling_function = Qnil;

  staticpro (&Qcatch_all_memory_full);
  /* Make sure Qcatch_all_memory_full is a unique object.  We could
     also use something like Fcons (Qnil, Qnil), but json.c treats any
     cons cell as error data, so use an uninterned symbol instead.  */
  Qcatch_all_memory_full
    = Fmake_symbol (build_pure_c_string ("catch-all-memory-full"));

  staticpro (&list_of_t);
  list_of_t = list1 (Qt);

  DEFSYM (Qdefvaralias, "defvaralias");
  DEFSYM (QCsuccess, ":success");
  DEFSYM (QCdebug_on_exit, ":debug-on-exit");
  DEFSYM (Qfunctionp, "functionp");
}
