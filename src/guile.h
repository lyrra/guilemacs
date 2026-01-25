SCM make_c_closure (SCM (*) (), void *, int, int);
void init_guile (void);

struct elisp_functions_ptr {
  SCM f_car;
  SCM f_cdr;
};

extern struct elisp_functions_ptr elisp_functions_ptr;

#define GUILECALL1(name, a1) \
  scm_call_1 (scm_variable_ref (elisp_functions_ptr.f_ ## name), a1)
