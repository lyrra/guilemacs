#ifndef EMACS_ALLOC_H
#define EMACS_ALLOC_H

#define UNGCPRO
#define staticpro(x)
#define inhibit_garbage_collection() 0
//#define unbind_to(count, val) (val)
//#define	record_unwind_protect_ptr (xfree, ptr)
//#define	record_unwind_protect_array (lispObj, nelt)
//#define record_unwind_protect_ptr_1 (fun, ptr, bool)
//WIP:
// record_unwind_protect_excursion (void);
// record_unwind_protect_nothing (void);
// clear_unwind_protect (ptrdiff_t);
// set_unwind_protect (ptrdiff_t, void (*) (Lisp_Object), Lisp_Object);
// set_unwind_protect_ptr (ptrdiff_t, void (*) (void *), void *);
#endif /* EMACS_ALLOC_H */
