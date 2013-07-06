#ifndef EMACS_ALLOC_H
#define EMACS_ALLOC_H

#define unbind_to(count, val) (val)
#define staticpro(x)
#define	record_unwind_protect_ptr (xfree, ptr)
#define	record_unwind_protect_array (buf, nelt)

#endif /* EMACS_ALLOC_H */
