// sum01_true-unreach-call_true-termination.c

/*@
    requires 0 <= n;
    requires n < 1000;
*/
int svcomp_19(int n) {
    int i = 0;
    int sn = 0;
    
    // Loop A
    /*@
        loop invariant i_11: i >= 0;

        loop invariant i_12: sn >= 0;

        loop invariant i_13: sn <= 2 * n;

        loop invariant i_14: sn == 2 * i;


        loop assigns i, sn;
    */
    for (i = 1; i <= n; i++) {
        sn = sn + 2;
    }
    
    //@ assert(sn == n * 2 || sn == 0);
    
    return 0;
}
