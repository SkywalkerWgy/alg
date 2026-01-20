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
        loop invariant i_8: i <= i + 1;

        loop invariant i_9: k >= 0 && k <= i;

        loop invariant i_10: j == 0 || j == n;

        loop invariant i_11: k == j + i - 1;

        loop invariant i_12: i >= 0 && i <= n;

        loop invariant i_13: k >= 0 && k <= n;

        loop invariant i_14: j >= 0 && j <= n;

        loop invariant i_15: i + j == n;


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
        loop invariant i_22: i <= i + 1;

        loop invariant i_23: k >= 0 && k <= i;

        loop invariant i_24: j == 0 || j == n;

        loop invariant i_25: k == j + i - 1;

        loop invariant i_26: i >= 0 && i <= n;

        loop invariant i_27: k >= 0 && k <= n;

        loop invariant i_28: j >= 0 && j <= n;

        loop invariant i_29: i + j == n;

        loop invariant i_30: \forall integer p; 0 <= p < i ==> \at(p, End_l) && \at(res[p], End_l) == true;

        loop invariant i_31: \exists integer p; 0 <= p < i && \at(p, End_l) && \at(res[p], End_l) == true;


        loop assigns t, i, k;
    */
    while (unknown2()) {
        t = i;
        i = i + 1;
        k = k + 1;
    }

    // Loop C
    /*@
        loop invariant i_16: k >= 0 && k <= n;

        loop invariant i_17: i >= 0 && i <= n;

        loop invariant i_18: j >= 0 && j <= n;

        loop invariant i_19: i + j == n;

        loop invariant i_20: \forall integer p; 0 <= p < i ==> \at(p, End_l) && \at(res[p], End_l) == true;

        loop invariant i_21: \exists integer p; 0 <= p < i && \at(p, End_l) && \at(res[p], End_l) == true;


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
