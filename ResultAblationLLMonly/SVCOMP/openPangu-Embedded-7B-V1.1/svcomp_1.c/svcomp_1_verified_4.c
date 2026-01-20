int svcomp_1() {
    int x = 1;
    int y = 0;
    // Loop A
    /*@
        loop invariant i_9: y < 1000;


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