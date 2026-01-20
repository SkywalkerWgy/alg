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
        loop invariant i_14: flag ==> (j == 2*a + 1);

        loop invariant i_15: (!flag) ==> (j == 2*a + 2);

        loop invariant i_16: i == 2*a + (flag ? 0 : 1);

        loop invariant i_17: b == a*a + a*(flag ? 0 : 1);


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