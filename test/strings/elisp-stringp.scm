;;; test/strings/elisp-stringp.scm --- the (emacs strings) predicate arms.
;;;
;;; `elisp-stringp' and `elisp-char-or-string-p' in mod/emacs/strings.scm
;;; each hold two arms:
;;;
;;;   (if (or (string? object)
;;;           (and (defined? 'emacs-string-predicate)
;;;                ((@ (emacs-string) emacs-string-predicate) object)))
;;;       #t #nil)
;;;
;;; The SECOND arm is the emacs-string wrapper path (Phase 2).  It is
;;; unreachable from an elisp `stringp' test, for two reasons, which is
;;; why test/pre/stringp.scm cannot cover it however many cases it adds:
;;;
;;;   `or' short-circuits.  For a real string (string? object) is true,
;;;   so the second arm is never evaluated -- every positive case stops
;;;   at the first arm.
;;;
;;;   `defined?' resolves against the DYNAMIC current module.  Its
;;;   argument is the bare symbol `emacs-string-predicate', so the guard
;;;   is true only when the CALLER's current module makes that name
;;;   visible.  Called from elisp, or from a module that does not import
;;;   (emacs text-properties), the guard is false and the second arm is
;;;   skipped again.  That is why (stringp 42) returns nil in a plain
;;;   batch emacs instead of failing.
;;;
;;; So the arm needs BOTH a non-string argument AND a current module
;;; where the predicate is visible.  This corpus drives exactly that: it
;;; sets the current module and calls the module procedure directly.
;;;
;;; The reachable arm must return nil for a non-string, like the first
;;; arm does.  It must not raise.  `(@ (emacs-string) ...)' names the
;;; module (emacs-string), which does not exist -- the predicate lives
;;; in (emacs text-properties) -- so resolve-module gives #f,
;;; module-variable is handed #f where it needs a module, and the call
;;; raises wrong-type-arg instead of answering.
;;;
;;; The live route is the same one: (emacs kbd-buffer) calls into
;;; (emacs strings) during kill-emacs, and its current module makes the
;;; predicate visible, so the shutdown path raises.  Nothing fails
;;; because of it -- the raise lands on stderr -- which is what this
;;; corpus fixes.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test;
;;; see test/strings/elisp-stringp.el.

(use-modules (emacs strings))
(use-modules (emacs text-properties))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define strings-module (resolve-module '(emacs strings)))

(define (predicate name)
  "The procedure NAME of (emacs strings)."
  (module-ref strings-module name))

(define (call-in-module module-name proc obj)
  "Apply PROC to OBJ with the current module set to MODULE-NAME.

The guard inside the predicate is (defined? 'emacs-string-predicate),
which reads the dynamic current module, so the module in force at the
call decides whether the wrapper arm is reachable at all.  Return the
value, or (threw KEY) when the call raises."
  (catch #t
    (lambda ()
      (save-module-excursion
       (lambda ()
         (set-current-module (resolve-module module-name))
         (proc obj))))
    (lambda (key . args) (list 'threw key))))

(define (visible-in? module-name)
  "Non-nil when emacs-string-predicate is visible from MODULE-NAME."
  (save-module-excursion
   (lambda ()
     (set-current-module (resolve-module module-name))
     (defined? 'emacs-string-predicate))))

;;; --- The precondition ------------------------------------------------
;;;
;;; These two make the rest meaningful.  If the predicate stops being
;;; visible from these modules the guard goes false, the wrapper arm
;;; becomes unreachable, and the checks below would pass for the wrong
;;; reason -- so pin the precondition instead of assuming it.

(check "strings/guard-visible-from-strings" #t
       (and (visible-in? '(emacs strings)) #t))
(check "strings/guard-visible-from-text-properties" #t
       (and (visible-in? '(emacs text-properties)) #t))

;;; --- The reachable arm must answer, not raise -------------------------

(check "strings/stringp-non-string-from-strings" #nil
       (call-in-module '(emacs strings) (predicate 'elisp-stringp) 42))
(check "strings/stringp-non-string-from-text-properties" #nil
       (call-in-module '(emacs text-properties)
                       (predicate 'elisp-stringp) 42))
(check "strings/char-or-string-p-non-string-from-strings" #nil
       (call-in-module '(emacs strings)
                       (predicate 'elisp-char-or-string-p) (list 1 2)))
(check "strings/char-or-string-p-non-string-from-text-properties" #nil
       (call-in-module '(emacs text-properties)
                       (predicate 'elisp-char-or-string-p) (list 1 2)))

;;; --- The first arm still works ----------------------------------------
;;;
;;; The controls.  A real string stops at (string? object), so these pass
;;; whatever the wrapper arm does; they catch a fix that breaks the
;;; ordinary path while repairing the broken one.

(check "strings/stringp-string-from-strings" #t
       (call-in-module '(emacs strings) (predicate 'elisp-stringp) "hi"))
(check "strings/char-or-string-p-string-from-strings" #t
       (call-in-module '(emacs strings)
                       (predicate 'elisp-char-or-string-p) "hi"))
(check "strings/char-or-string-p-char-from-strings" #t
       (call-in-module '(emacs strings)
                       (predicate 'elisp-char-or-string-p) 65))

;;; --- The wrapper arm answers for a real wrapper -----------------------
;;;
;;; `emacs-string-predicate' is the point of the arm, so drive it with
;;; the object it exists for.  A plain non-string is not an emacs-string,
;;; so the predicate says no and the whole `or' is nil -- the same answer
;;; as above, but reached THROUGH the predicate rather than past it.

(check "strings/wrapper-predicate-rejects-non-string" #f
       (call-in-module '(emacs text-properties)
                       (module-ref (resolve-module '(emacs text-properties))
                                   'emacs-string-predicate)
                       42))
