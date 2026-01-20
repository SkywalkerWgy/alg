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
        loop invariant i_6: a == b - j + 2*i;

        loop invariant i_7: flag == 0 => i == 1;

        loop invariant i_8: flag == 1 => i == 0;

        loop invariant i_9: j == 1;

        loop invariant i_10: j % 2 == 1;

        loop invariant i_11: i % 2 == 0 => j == j + 2;

        loop invariant i_12: i % 2 == 1 => j == j + 1;


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