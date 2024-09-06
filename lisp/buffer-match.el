(defvar buffer-match-p--past-warnings nil)

(defun buffer-match-p (condition buffer-or-name &rest args)
  "Return non-nil if BUFFER-OR-NAME matches CONDITION.
CONDITION is either:
- the symbol t, to always match,
- the symbol nil, which never matches,
- a regular expression, to match a buffer name,
- a predicate function that takes BUFFER-OR-NAME plus ARGS as
  arguments, and returns non-nil if the buffer matches,
- a cons-cell, where the car describes how to interpret the cdr.
  The car can be one of the following:
  * `derived-mode': the buffer matches if the buffer's major mode
    is derived from the major mode in the cons-cell's cdr.
  * `major-mode': the buffer matches if the buffer's major mode
    is eq to the cons-cell's cdr.  Prefer using `derived-mode'
    instead when both can work.
  * `category': when this function is called from `display-buffer',
    the buffer matches if the caller of `display-buffer' provides
    `(category . SYMBOL)' in its ACTION argument, and SYMBOL is `eq'
    to the cons-cell's cdr.
  * `not': the cadr is interpreted as a negation of a condition.
  * `and': the cdr is a list of recursive conditions, that all have
    to be met.
  * `or': the cdr is a list of recursive condition, of which at
    least one has to be met."
  (letrec
      ((buffer (get-buffer buffer-or-name))
       (match
        (lambda (conditions)
          (catch 'match
            (dolist (condition conditions)
              (when (pcase condition
                      ('t t)
                      ((pred stringp)
                       (string-match-p condition (buffer-name buffer)))
                      ((pred functionp)
                       (if (cdr args)
                           ;; New in Emacs>29.1. no need for compatibility hack.
                           (apply condition buffer-or-name args)
                         (condition-case-unless-debug err
                             (apply condition buffer-or-name args)
                           (wrong-number-of-arguments
                            (unless (member condition
                                            buffer-match-p--past-warnings)
                              (message "%s" (error-message-string err))
                              (push condition buffer-match-p--past-warnings))
                            (apply condition buffer-or-name
                                   (if args nil '(nil)))))))
                      (`(category . ,category)
                       (eq (alist-get 'category (cdar args)) category))
                      (`(major-mode . ,mode)
                       (eq
                        (buffer-local-value 'major-mode buffer)
                        mode))
                      (`(derived-mode . ,mode)
                       (provided-mode-derived-p
                        (buffer-local-value 'major-mode buffer)
                        mode))
                      (`(not . ,cond)
                       (not (funcall match cond)))
                      (`(or . ,args)
                       (funcall match args))
                      (`(and . ,args)
                       (catch 'fail
                         (dolist (c args)
                           (unless (funcall match (list c))
                             (throw 'fail nil)))
                         t)))
                (throw 'match t)))))))
    (funcall match (list condition))))

(defun match-buffers (condition &optional buffers &rest args)
  "Return a list of buffers that match CONDITION, or nil if none match.
See `buffer-match-p' for various supported CONDITIONs.
By default all buffers are checked, but the optional
argument BUFFERS can restrict that: its value should be
an explicit list of buffers to check.
Optional arguments ARGS are passed to `buffer-match-p', for
predicate conditions in CONDITION."
  (let (bufs)
    (dolist (buf (or buffers (buffer-list)))
      (when (apply #'buffer-match-p condition (get-buffer buf) args)
        (push buf bufs)))
    bufs))
