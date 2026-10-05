;;; dired.scm --- M49 imp-2: the thin wrappers over the four typed C
;;;                leaves of src/dired.c ((emacs dired))
;;;
;;; The directory / attribute policy of src/dired.c has four movable
;;; parts: the listing policy (G1), the completion policy (G2), and the
;;; attribute predicate (G3) (docs/m49-plan.org section 3.2).  M49
;;; imp-2 adds one typed C leaf per part and this module of thin
;;; wrappers.  It moves no policy; imp-3 (G1 and G2) and imp-4 (G3)
;;; rewire the C hubs onto the leaves and move the choice into Scheme.
;;;
;;;   (dired-listing-names directory full match nosort)
;;;        -> the ordered name list of DIRECTORY as a plain list of
;;;           strings.  It serves both G1 hubs, `directory-files' and
;;;           `directory-files-and-attributes'.
;;;   (dired-file-name-completion directory file predicate)
;;;        -> one plain string, t, or #f.
;;;   (dired-file-name-all-completions directory file)
;;;        -> a plain list of strings.
;;;   (dired-file-attributes-lessp name1 name2)
;;;        -> a plain boolean.
;;;
;;; Every value is plain: a string, a boolean, #f, or a list of plain
;;; strings.  No struct dirent *, struct stat *, DIR *, char *, struct
;;; passwd *, struct group *, Lisp_Object, or attribute list crosses
;;; the layer (the M42 rule).  The C leaf keeps the mechanism: the
;;; readdir loop, the scmp compare, the sort, and the DECODE_FILE call.
;;;
;;; The G3 leaf narrows the argument shape: the block
;;; file-attributes-lessp takes two attribute lists and extracts Fcar
;;; of each, so the C hub keeps the Fcar extraction and the leaf takes
;;; two plain file names (docs/kb.org leaf-may-narrow-the-argument-shape).
;;;
;;; This module holds no policy, no FFI call, and no raw syscall.  Each
;;; wrapper is a one-line call to its leaf.
;;;
;;; Conventions (identical to M9-M48): #nil is elisp nil; no
;;; module-level mutable state.

(define-module (emacs dired)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (dired-listing-names
            dired-file-name-completion
            dired-file-name-all-completions
            dired-file-attributes-lessp))

;; The four C leaves (src/dired.c).
(defelisp %--dired-listing-names             --dired-listing-names)
(defelisp %--dired-file-name-completion      --dired-file-name-completion)
(defelisp %--dired-file-name-all-completions --dired-file-name-all-completions)
(defelisp %--dired-file-attributes-lessp     --dired-file-attributes-lessp)

;; Return the ordered name list of DIRECTORY as a plain list of
;; strings.  DIRECTORY is a plain string; FULL, MATCH, and NOSORT are
;; the plain arguments of `directory-files'.
(define (dired-listing-names directory full match nosort)
  ((force %--dired-listing-names) directory full match nosort))

;; Complete FILE in directory DIRECTORY and return one plain string, t
;; for a sole exact match, or #f.
(define (dired-file-name-completion directory file predicate)
  ((force %--dired-file-name-completion) directory file predicate))

;; Return all completions of FILE in directory DIRECTORY as a plain
;; list of strings.
(define (dired-file-name-all-completions directory file)
  ((force %--dired-file-name-all-completions) directory file))

;; Return t when the plain file name NAME1 sorts before NAME2 with
;; `string-lessp', else #f.
(define (dired-file-attributes-lessp name1 name2)
  ((force %--dired-file-attributes-lessp) name1 name2))
