extern unsigned __VERIFIER_nondet_uint();
extern void __assert_fail();

extern int __VERIFIER_nondet_int(void);

void __VERIFIER_assert(int cond) {
  if (!cond) {
    __assert_fail();
  }
}
int main() {
  unsigned n =  __VERIFIER_nondet_uint();
  unsigned x =  __VERIFIER_nondet_uint();
  unsigned y = n - x;
  while(x > y) {
    x--; y++;
    __VERIFIER_assert(x + y != n); 
  }
  return 0;
}