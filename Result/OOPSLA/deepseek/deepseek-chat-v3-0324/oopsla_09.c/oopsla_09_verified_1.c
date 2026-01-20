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

        loop invariant i_3: k >= 0;

        loop invariant i_4: t == \at(i, Pre) ==> k == 0;

        loop invariant i_5: \forall integer x; \at(i, Pre) <= x < i ==> \at(k, Pre) + x - \at(i, Pre) == k;


        loop assigns t, i, k;
    */
    while (unknown2()) {
        t = i;
        i = i + 1;
        k = k + 1;
    }

    // Loop C
    /*@
        loop invariant i_6: i == \at(i, Pre);

        loop invariant i_7: k == \at(k, Pre);

        loop invariant i_8: t == \at(t, Pre);

        loop invariant i_9: pvlen == \at(pvlen, Pre);


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
