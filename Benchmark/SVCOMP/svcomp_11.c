// hhk2008_true-unreach-call.c

/*@
    requires a < 1000000;
    requires 0 <= b && b <= 1000000;
*/
int svcomp_11(int a, int b) {

    int res, cnt;

    res = a;
    cnt = b;

    /*@
        loop assigns cnt, res;
    */
    while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    //@ assert res == a + b;
    
    return 0;
}
