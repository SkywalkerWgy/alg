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
        loop invariant i_0: a == (i - (flag ? 0 : 1))/2;

        loop invariant i_1: b == (j - 1 - (flag ? 0 : 1)) * (j - (flag ? 0 : 1)) / 4 + ((j - (flag ? 0 : 1)) % 2 == 0 ? 0 : (j - (flag ? 0 : 1) + 1)/2);


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