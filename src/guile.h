SCM make_c_closure (SCM (*) (), void *, int, int);
void init_guile (void);

/* M2: smob type tag for KBOARD foreign-object wrapping.
   Defined in guile.c, initialized in init_guile. */
extern scm_t_bits kboard_tag;

struct elisp_functions_ptr {
  SCM f_car;
  SCM f_cdr;
};

extern struct elisp_functions_ptr elisp_functions_ptr;

#define GUILECALL1(name, a1) \
  scm_call_1 (scm_variable_ref (elisp_functions_ptr.f_ ## name), a1)

extern uint64_t c_to_scheme_crossings;

/* Count every C→Scheme crossing via scm_call_*.
   (scm_call_N)(...) suppresses macro re-expansion. */
#define SCM_CALL_0(fn)              (c_to_scheme_crossings++, (scm_call_0)(fn))
#define SCM_CALL_1(fn,a)            (c_to_scheme_crossings++, (scm_call_1)(fn,a))
#define SCM_CALL_2(fn,a,b)          (c_to_scheme_crossings++, (scm_call_2)(fn,a,b))
#define SCM_CALL_3(fn,a,b,c)        (c_to_scheme_crossings++, (scm_call_3)(fn,a,b,c))
#define SCM_CALL_4(fn,a,b,c,d)      (c_to_scheme_crossings++, (scm_call_4)(fn,a,b,c,d))
#define SCM_CALL_5(fn,a,b,c,d,e)    (c_to_scheme_crossings++, (scm_call_5)(fn,a,b,c,d,e))
#define SCM_CALL_7(fn,a,b,c,d,e,f,g) (c_to_scheme_crossings++, (scm_call_7)(fn,a,b,c,d,e,f,g))
#define SCM_CALL_N(fn,args,n)       (c_to_scheme_crossings++, (scm_call_n)(fn,args,n))
