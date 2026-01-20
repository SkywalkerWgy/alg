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
        loop invariant i_0: flag != 0 ==> a == b;

        loop invariant i_3: flag != 0 ==> a - b == 0;

        loop invariant i_4: flag != 0 ==> j - i == 1;

        loop invariant i_5: flag != 0 ==> i % 2 == 0;

        loop invariant i_7: flag == 0 || (a == b && j - i == 1 && i % 2 == 0);

        loop invariant i_11: flag != 0 ==> (a == b && j == i + 1);

        loop invariant i_12: flag != 0 ==> (j == 1 + 2 * a && i % 2 == 0);

        loop invariant i_13: flag == 0 || (a == b && j == i + 1 && i % 2 == 0);

        loop invariant i_14: flag != 0 ==> (a == b && j == i + 1 && i % 2 == 0);


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