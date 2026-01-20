#define SZ 2048

void svcomp_3() {
  int A[SZ];
  int B[SZ];
  int i;
  int tmp;

    // Loop A
  /*@
        loop invariant i_6: i <= SZ;


        loop assigns i;
        loop assigns B[0..1023];
    */
  for (i = 0; i < SZ; i++) {
    tmp = A[i];
    B[i] = tmp;
  }

  //@ assert A[SZ/2] == B[SZ/2];
}