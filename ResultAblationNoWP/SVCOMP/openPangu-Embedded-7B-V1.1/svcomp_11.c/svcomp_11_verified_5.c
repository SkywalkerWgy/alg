// hhk2008_true-unreach-call.c

/*@
    requires a < 1000000;
    requires 0 <= b && b <= 1000000;
*/
int svcomp_11(int a, int b) {

    int res, cnt;

    res = a;
    cnt = b;

    // Loop A
    /*@
        loop invariant i_9: cnt >= 0 && cnt <= b;

        loop invariant i_10: res >= 0 && res <= a + b;

        loop invariant i_11: res == a + cnt;


        loop assigns cnt, res;
    */
    while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    //@ assert res == a + b;
    
    return 0;
}
