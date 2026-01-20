void svcomp_2() {
    int A[2048];
    int i;

    // Loop A
    /*@
        loop invariant i_2: i < 1024;

        loop invariant i_3: A[i] == i;


        loop assigns i;
        loop assigns A[0..1023];
    */
    for (i = 0; i < 1024; i++) {
        A[i] = i;
    }

    //@ assert A[1023] == 1023;
}