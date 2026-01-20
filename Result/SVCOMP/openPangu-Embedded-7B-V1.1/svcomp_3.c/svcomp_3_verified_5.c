#define SZ 2048

void svcomp_3() {
  int A[SZ];
  int B[SZ];
  int i;
  int tmp;

    // Loop A
  /*@
        loop invariant i_0: 0 <= i < SZ;

        loop invariant i_5: i >= 0;

        loop invariant i_6: i < SZ;

        loop invariant i_8: A[0] == B[0];

        loop invariant i_9: A[i] == B[i];


        loop assigns i;
        loop assigns B[0..1023];
    */
  for (i = 0; i < SZ; i++) {
    tmp = A[i];
    B[i] = tmp;
  }

  //@ assert A[SZ/2] == B[SZ/2];
}