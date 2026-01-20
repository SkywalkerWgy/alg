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
        loop invariant i_51: i <= i + 1;

        loop invariant i_52: k <= k + 1;

        loop invariant i_53: t == t;

        loop invariant i_54: true;

        loop invariant i_55: k >= 0;


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
        loop invariant i_60: i <= i + 1;

        loop invariant i_61: k <= k + 1;

        loop invariant i_62: t == t;

        loop invariant i_63: true;

        loop invariant i_64: k >= 0;

        loop invariant i_65: j <= j + 1;

        loop invariant i_66: \forall integer k; 0 <= k < i ==> max >= a[k];


        loop assigns t, i, k;
    */
    while (unknown2()) {
        t = i;
        i = i + 1;
        k = k + 1;
    }

    // Loop C
    /*@
        loop invariant i_56: k >= 0;

        loop invariant i_57: i <= i + 1;

        loop invariant i_58: j <= j + 1;

        loop invariant i_59: \forall integer k; 0 <= k < i ==> max >= a[k];


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
