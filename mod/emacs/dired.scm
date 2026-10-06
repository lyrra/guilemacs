;;; dired.scm --- the directory / attribute policy of src/dired.c
;;;                ((emacs dired))
;;;
;;; The directory / attribute boundary of src/dired.c has three movable
;;; parts: the listing policy (G1), the completion policy (G2), and the
;;; attribute predicate (G3) (docs/m49-plan.org section 3.2).  M49 imp-2
;;; added one typed C leaf per part and thin wrappers.  M49 imp-3 moved
;;; the G1 listing decision HERE.  M49 imp-4 moved the G3 attribute
;;; predicate HERE; G2 returns A2 (brief.org section 7.5), so the
;;; completion policy stays in C and G2 still calls its C leaves.
;;;
;;;   (dired-listing-names names directory full match nosort count)
;;;        -> the ordered name list of DIRECTORY as a plain list of
;;;           strings.  NAMES is the raw readdir-ordered name list from
;;;           the C mechanism dired_read_names_1.  The module computes
;;;           the separator, the full join, the match, the count, and
;;;           the sort key (brief.org section 7.2).
;;;   (dired-file-name-completion directory file predicate)
;;;        -> one plain string, t, or #f.
;;;   (dired-file-name-all-completions directory file)
;;;        -> a plain list of strings.
;;;   (dired-file-attributes-lessp name1 name2)
;;;        -> a plain boolean.
;;;
;;; Every value is plain: a string, a boolean, #f, or a list of plain
;;; strings.  No struct dirent *, struct stat *, DIR *, char *, struct
;;; passwd *, struct group *, Lisp_Object, or attribute list crosses the
;;; layer (the M42 rule).  The C hub keeps the mechanism: the readdir
;;; loop (dired_read_names_1), the scmp compare, and the DECODE_FILE
;;; call.  The G1 policy calls the elisp subrs `string-match' and
;;; `string-lessp' by their function slots; it holds no FFI call and no
;;; raw syscall.
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

;; The 2 C leaves that remain after imp-4 (src/dired.c).  imp-3 deleted
;; the G1 listing leaf; imp-4 deleted the G3 attribute-predicate leaf.
;; Its decision is now dired-file-attributes-lessp.
(defelisp %--dired-file-name-completion      --dired-file-name-completion)
(defelisp %--dired-file-name-all-completions --dired-file-name-all-completions)

;; The elisp subrs the G1 policy uses.  `symbol-function' looks them up
;; by name, so the module needs no new C surface.
(defelisp %string-match string-match)
(defelisp %string-lessp  string-lessp)

;; Elisp truthiness for a value that crosses the layer.  The C hub
;; passes Qt or Qnil, but a Scheme caller may pass #f, and #f must read
;; false.  Guile treats #nil as true, so fold it to #f here.
(define (dired--true? x)
  (not (or (eq? x #nil) (eq? x #f))))

;; An elisp list terminator: the Guile empty list or the elisp nil.
(define (dired--end? lst)
  (or (null? lst) (eq? lst #nil)))

;; Elisp `string-match-p': a true value when REGEXP matches STRING
;; anywhere (the C code uses a search, fast_string_match_internal, so the
;; match is not anchored).  The 4th argument INHIBIT-MODIFY is #t: the
;; subr must NOT clobber the match data, exactly as the old C code did
;; with fast_string_match_internal (src/search.c).  A 2-argument call
;; would change the global match data (the D1 defect, cr.org section
;; 5.1).  The runtime bridges #t to elisp t and #nil to elisp nil.
(define (dired--string-match-p regexp string)
  (dired--true? ((force %string-match) regexp string #nil #t)))

;; Elisp `string-lessp': a Guile boolean, true when A sorts before B.
(define (dired--string-lessp a b)
  (dired--true? ((force %string-lessp) a b)))

;; The separator / full join: DIRECTORY and NAME, with one separator
;; only when DIRECTORY is empty or its last character is not a separator.
(define (dired--join directory name)
  (let* ((n (string-length directory))
         (needsep (or (= n 0)
                      (not (char=? (string-ref directory (- n 1)) #\/)))))
    (if needsep
        (string-append directory "/" name)
        (string-append directory name))))

;; A Guile ()-terminated copy of the list LST.
(define (dired--proper lst)
  (if (dired--end? lst)
      '()
      (cons (car lst) (dired--proper (cdr lst)))))

;; Re-terminate a Guile ()-list with elisp #nil (the module convention).
(define (dired--nil-terminate lst)
  (if (null? lst)
      #nil
      (begin
        (let loop ((tail lst))
          (if (null? (cdr tail))
              (set-cdr! tail #nil)
              (loop (cdr tail))))
        lst)))

;; The first N elements of LST, in order, as a Guile ()-list.
(define (dired--take lst n)
  (if (or (<= n 0) (dired--end? lst))
      '()
      (cons (car lst) (dired--take (cdr lst) (- n 1)))))

;; Compute the G1 listing decision.  NAMES is the raw readdir-ordered
;; name list; DIRECTORY is the expanded directory string; FULL, MATCH,
;; NOSORT, and COUNT are the plain `directory-files' arguments.  Return a
;; plain list of plain strings: the names in readdir order, filtered by
;; MATCH, truncated to COUNT names, joined to DIRECTORY when FULL, and
;; sorted with `string-lessp' when NOSORT is nil.
(define (dired-listing-names names directory full match nosort count)
  (let* ((raw (dired--proper names))
         ;; 2. Match: keep the names whose non-directory part matches the
         ;;    regexp MATCH.  The raw name is the non-directory part.
         (matched (if (dired--true? match)
                      (filter (lambda (n) (dired--string-match-p match n)) raw)
                      raw))
         ;; 3. Count: keep the first COUNT names of the readdir order.
         (counted (if (and (integer? count) (>= count 0))
                      (dired--take matched count)
                      matched))
         ;; 1. Separator / full join.
         (joined (if (dired--true? full)
                     (map (lambda (n) (dired--join directory n)) counted)
                     counted))
         ;; 4. Sort key: sort with `string-lessp' when NOSORT is nil.
         (ordered (if (dired--true? nosort)
                      joined
                      (sort joined dired--string-lessp))))
    (dired--nil-terminate ordered)))

;; Complete FILE in directory DIRECTORY and return one plain string, t
;; for a sole exact match, or #f.
(define (dired-file-name-completion directory file predicate)
  ((force %--dired-file-name-completion) directory file predicate))

;; Return all completions of FILE in directory DIRECTORY as a plain
;; list of strings.
(define (dired-file-name-all-completions directory file)
  ((force %--dired-file-name-all-completions) directory file))

;; Return t (#t) when the plain file name NAME1 sorts before NAME2 with
;; `string-lessp', else nil (#nil).  The G3 attribute predicate decision
;; runs HERE (M49 imp-4); the C hub keeps the Fcar extraction and passes
;; the two plain names (brief.org section 7.4).
(define (dired-file-attributes-lessp name1 name2)
  (if (dired--string-lessp name1 name2) #t #nil))
