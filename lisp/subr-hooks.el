
;;;; Hook manipulation functions.

(defun add-hook (hook function &optional depth local)
  ;; Note: the -100..100 depth range is arbitrary and was chosen to match the
  ;; range used in add-function.
  "Add to the value of HOOK the function FUNCTION.
FUNCTION is not added if already present.

The place where the function is added depends on the DEPTH
parameter.  DEPTH defaults to 0.  By convention, it should be
a number between -100 and 100 where 100 means that the function
should be at the very end of the list, whereas -100 means that
the function should always come first.
Since nothing is \"always\" true, don't use 100 nor -100.
When two functions have the same depth, the new one gets added after the
old one if depth is strictly positive and before otherwise.

For backward compatibility reasons, a symbol other than nil is
interpreted as a DEPTH of 90.

The optional fourth argument, LOCAL, if non-nil, says to modify
the hook's buffer-local value rather than its global value.
This makes the hook buffer-local, and it makes t a member of the
buffer-local value.  That acts as a flag to run the hook
functions of the global value as well as in the local value.

HOOK should be a symbol, and FUNCTION may be any valid function.  If
HOOK is void, it is first set to nil.  If HOOK's value is a single
function, it is changed to a list of functions."
  (or (boundp hook) (set hook nil))
  (or (default-boundp hook) (set-default hook nil))
  (unless (numberp depth) (setq depth (if depth 90 0)))
  (if local (unless (local-variable-if-set-p hook)
	      (set (make-local-variable hook) (list t)))
    ;; Detect the case where make-local-variable was used on a hook
    ;; and do what we used to do.
    (unless (and (consp (symbol-value hook)) (memq t (symbol-value hook)))
      (setq local t)))
  (let ((hook-value (if local (symbol-value hook) (default-value hook))))
    ;; If the hook value is a single function, turn it into a list.
    (when (or (not (listp hook-value)) (functionp hook-value))
      (setq hook-value (list hook-value)))
    ;; Do the actual addition if necessary
    (unless (member function hook-value)
      ;(when (stringp function)          ;FIXME: Why?
	;(setq function (purecopy function)))
      ;; FIX-2023022-LAV: wont work, seems to use perhaps an yet undefined macro
      '(when (or (get hook 'hook--depth-alist) (not (zerop depth)))
        ;; Note: The main purpose of the above `when' test is to avoid running
        ;; this `setf' before `gv' is loaded during bootstrap.
        (let ((h (get hook 'hook--depth-alist)))
          (setf (alist-get function h 0 'remove #'equal) depth)))
      (setq hook-value
	    (if (< 0 depth)
		(append hook-value (list function))
	      (cons function hook-value)))
      (let ((depth-alist (get hook 'hook--depth-alist)))
        (when depth-alist
          (setq hook-value
                (sort (if (< 0 depth) hook-value (copy-sequence hook-value))
                      (lambda (f1 f2)
                        (< (alist-get f1 depth-alist 0 nil #'equal)
                           (alist-get f2 depth-alist 0 nil #'equal))))))))
    ;; Set the actual variable
    (if local
	(progn
	  ;; If HOOK isn't a permanent local,
	  ;; but FUNCTION wants to survive a change of modes,
	  ;; mark HOOK as partially permanent.
	  (and (symbolp function)
	       (get function 'permanent-local-hook)
	       (not (get hook 'permanent-local))
	       (put hook 'permanent-local 'permanent-local-hook))
	  (set hook hook-value))
      (set-default hook hook-value))))

(defun remove-hook (hook function &optional local)
  "Remove from the value of HOOK the function FUNCTION.
HOOK should be a symbol, and FUNCTION may be any valid function.  If
FUNCTION isn't the value of HOOK, or, if FUNCTION doesn't appear in the
list of hooks to run in HOOK, then nothing is done.  See `add-hook'.

The optional third argument, LOCAL, if non-nil, says to modify
the hook's buffer-local value rather than its default value."
  (or (boundp hook) (set hook nil))
  (or (default-boundp hook) (set-default hook nil))
  ;; Do nothing if LOCAL is t but this hook has no local binding.
  (unless (and local (not (local-variable-p hook)))
    ;; Detect the case where make-local-variable was used on a hook
    ;; and do what we used to do.
    (when (and (local-variable-p hook)
	       (not (and (consp (symbol-value hook))
			 (memq t (symbol-value hook)))))
      (setq local t))
    (let ((hook-value (if local (symbol-value hook) (default-value hook))))
      ;; Remove the function, for both the list and the non-list cases.
      (if (or (not (listp hook-value)) (eq (car hook-value) 'lambda))
	  (if (equal hook-value function) (setq hook-value nil))
	(setq hook-value (delete function (copy-sequence hook-value))))
      ;; If the function is on the global hook, we need to shadow it locally
      ;;(when (and local (member function (default-value hook))
      ;;	       (not (member (cons 'not function) hook-value)))
      ;;  (push (cons 'not function) hook-value))
      ;; Set the actual variable
      (if (not local)
	  (set-default hook hook-value)
	(if (equal hook-value '(t))
	    (kill-local-variable hook)
	  (set hook hook-value))))))

(add-hook 'kill-buffer-query-functions 'process-kill-buffer-query-function)
