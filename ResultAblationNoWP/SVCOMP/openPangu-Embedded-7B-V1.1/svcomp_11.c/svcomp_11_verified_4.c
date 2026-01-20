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
        loop invariant i_6: 1 <= cnt;

        loop invariant i_7: cnt >= 0;

        loop invariant i_8: res == a + b - cnt;


        loop assigns cnt, res;
    */
    while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    //@ assert res == a + b;
    
    return 0;
}
