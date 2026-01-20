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

        loop invariant i_11: i <= SZ/2 - 1;

        loop invariant i_12: A[SZ/2] == B[SZ/2];

        loop invariant i_13: i == 0;

        loop invariant i_14: i >= 0 && i < SZ && A[i] == B[i];

        loop invariant i_15: i >= 0 && i < SZ;


        loop assigns i;
        loop assigns B[0..1023];
    */
  for (i = 0; i < SZ; i++) {
    tmp = A[i];
    B[i] = tmp;
  }

  //@ assert A[SZ/2] == B[SZ/2];
}