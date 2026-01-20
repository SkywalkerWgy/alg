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
        loop invariant i_42: i >= 0 && i <= unknown1();

        loop invariant i_43: i >= 0 && i < unknown2();

        loop invariant i_44: j >= 0 && j <= n && k >= 0 && i >= 0 && i <= j;


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
        loop invariant i_46: i >= 0 && i < unknown2();


        loop assigns t, i, k;
    */
    while (unknown2()) {
        t = i;
        i = i + 1;
        k = k + 1;
    }

    // Loop C
    /*@
        loop invariant i_45: j >= 0 && j <= n && k >= 0 && i >= 0 && i <= j;


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
