void svcomp_2() {
    int A[2048];
    int i;

    // Loop A
    /*@
        loop invariant i_5: 0 <= i < 1024;


        loop assigns i;
        loop assigns A[0..1023];
    */
    for (i = 0; i < 1024; i++) {
        A[i] = i;
    }

    //@ assert A[1023] == 1023;
}