// Source: Isil Dillig, Thomas Dillig, Boyang Li, Ken McMillan: "Inductive
// Invariant Generation via Abductive Inference", OOPSLA 2013.
#include "assert.h"
int unknown1();

int svcomp_8(int flag) {
    unsigned int i, j, a, b;
    a = 0;
    b = 0;
    j = 1;

    if (flag) {
        i = 0;
    } else {
        i = 1;
    }

    // Loop A
    /*@
        loop invariant i_0: ``` loop invariant flag ==> (i == 2*a);

        loop invariant i_1: flag ==> (i == 2*a);

        loop invariant i_2: !flag ==> (i == 2*a + 1);

        loop invariant i_3: j == a + 1;

        loop invariant i_4: flag ==> (b == a);

        loop invariant i_5: !flag ==> (b == a*(a + 1)/2);


        loop assigns a, b, i, j;
    */
    while (unknown1()) {
        a++;
        b += (j - i);
        i += 2;
        if (i%2 == 0) {
            j += 2;
        } else {
            j++;
        }
    }
    if (flag) {
        //@ assert a == b;
    }
    return 0;
}