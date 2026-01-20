int unknown1();
int unknown2();
int unknown3();

/*
 * "fragtest_simple" from InvGen benchmark suite
 */


void oopsla_09(){
    int i, pvlen;
    int t;
    int k = 0;
    int n;
    i = 0;

    // Loop A
    /*@
        loop invariant i_12: i >= 0;

        loop invariant i_13: pvlen >= 0 && pvlen <= i;

        loop invariant i_14: k >= 0 && k <= i;

        loop invariant i_15: j >= 0 && j <= n;

        loop invariant i_16: i >= j;

        loop invariant i_17: i + k <= i;

        loop invariant i_18: k - j <= i;

        loop invariant i_19: j < n && j >= 0;

        loop invariant i_20: n >= 0;


        loop assigns i;
    */
    while (unknown1())
        i = i + 1;
    
    if (i > pvlen) {
        pvlen = i;
    } 
    else {
    }
    i = 0;

    // Loop B
    /*@
        loop invariant i_30: i >= 0 && i <= n;

        loop invariant i_31: k >= 0 && k <= n - j;


        loop assigns t, i, k;
    */
    while (unknown2()) {
        t = i;
        i = i + 1;
        k = k + 1;
    }

    // Loop C
    /*@
        loop invariant i_21: j >= 0 && j < n && k >= 0 && k <= n;

        loop invariant i_22: j < n;

        loop invariant i_23: k == n - j;

        loop invariant i_24: i >= 0 && i <= n;

        loop invariant i_25: t == i;

        loop invariant i_26: t >= 0 && t <= n;

        loop invariant i_27: n >= 0 && n <= n;

        loop invariant i_28: j == n - i && i >= 0 && i <= n;

        loop invariant i_29: k == n - j && j >= 0 && j < n && k >= 0 && k <= n;


        loop assigns \nothing;
    */
    while (unknown3());

    int j = 0;
    n = i;

    /*@
        loop assigns j, i, k;
    */
    while (1) {
        //@ assert a_1: k >= 0;
        k = k - 1;
        i = i - 1;
        j = j + 1;
        if (j < n) {
        } 
        else {
            break;
        }
    }
}
