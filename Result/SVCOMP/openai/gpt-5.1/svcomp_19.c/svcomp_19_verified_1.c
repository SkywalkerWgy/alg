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
        loop invariant i_0: 0 <= n;

        loop invariant i_1: n < 1000;

        loop invariant i_2: 1 <= i && i <= n + 1;

        loop invariant i_3: sn == 2 * (i - 1);


        loop assigns i, sn;
    */
    for (i = 1; i <= n; i++) {
        sn = sn + 2;
    }
    
    //@ assert(sn == n * 2 || sn == 0);
    
    return 0;
}
