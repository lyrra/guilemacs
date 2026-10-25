;;; M60 imp-16 fixture for row 25:
;;; `normal-top-level-add-to-load-path' (lisp/startup.el :479).
;;;
;;; The 1 form is the call shape of lisp/subdirs.el :3: a quoted list of
;;; names.  The 2 names do NOT exist as directories on purpose -- the
;;; function splices `expand-file-name' results and never checks the
;;; file system (measured: 24 real names gave the same 24 joins).
;;;
;;; The CALLER owns the `default-directory' bind (lisp/startup.el :631).
;;; The suite therefore loads this fixture TWICE: once with no bind (the
;;; negative control, it must raise `void-variable') and once with the
;;; bind.  Order matters -- the elisp value slot has no "unbind".
(normal-top-level-add-to-load-path '("m60ntla" "m60ntlb"))
