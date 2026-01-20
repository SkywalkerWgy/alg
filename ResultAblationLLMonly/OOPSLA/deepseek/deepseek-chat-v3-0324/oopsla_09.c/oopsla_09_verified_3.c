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
        loop invariant i_0: i >= 0;

        loop invariant i_1: \forall integer x; 0 <= x < i ==> unknown1() != 0;


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
        loop invariant i_2: i == k;

        loop invariant i_3: i >= 0;

        loop invariant i_4: k >= 0;

        loop invariant i_9: s for Loop B: ``` loop invariant i == k;

        loop invariant i_10: \forall integer x; 0 <= x < i ==> unknown2() != 0;


        loop assigns t, i, k;
    */
    while (unknown2()) {
        t = i;
        i = i + 1;
        k = k + 1;
    }

    // Loop C
    /*@
        loop invariant i_5: \true;

        loop invariant i_6: i == k;

        loop invariant i_7: i >= 0;

        loop invariant i_8: k >= 0;


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
