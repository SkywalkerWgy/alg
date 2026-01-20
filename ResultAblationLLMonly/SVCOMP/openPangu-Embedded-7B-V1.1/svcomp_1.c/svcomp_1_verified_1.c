int svcomp_1() {
    int x = 1;
    int y = 0;
    // Loop A
    /*@
        loop invariant i_0: 1 <= x && 0 <= y;

        loop invariant i_1: y < 1000;

        loop invariant i_2: x >= y;

        loop invariant i_3: for the following loop. loop assigns y;


        loop assigns y;
        loop assigns x;
    */
    while (y < 1000 ) {
        x = x + y;
        y = y + 1;
    }
    //@ assert x >= y;
    return 0;
}