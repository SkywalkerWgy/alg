int svcomp_1() {
    int x = 1;
    int y = 0;
    // Loop A
    /*@
        loop invariant i_0: y <= 1000;

        loop invariant i_1: x >= y * (y - 1) / 2 + 1;


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