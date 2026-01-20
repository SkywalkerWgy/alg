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
        loop invariant i_0: i < unknown1();

        loop invariant i_1: i < unknown1() || i == 0;

        loop invariant i_2: i < unknown2();

        loop invariant i_3: k < unknown2();

        loop invariant i_4: k < unknown2() || k == 0;

        loop invariant i_5: i < n;

        loop invariant i_6: j >= 0;

        loop invariant i_7: k >= 0;

        loop invariant i_8: j < n || j == n;


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
        loop invariant i_10: k >= 0 && i >= 0;

        loop invariant i_11: j < n || j == n && k < unknown2();


        loop assigns t, i, k;
    */
    while (unknown2()) {
        t = i;
        i = i + 1;
        k = k + 1;
    }

    // Loop C
    /*@
        loop invariant i_9: k >= 0 && j >= 0;


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
