#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on "SYNERGY: A New Algorithm for Property Checking" by Gulavani et al.
 */

void oopsla_30() {

    int i, c;
    i = 0;
    c = 0;
    // Loop A
    /*@
        loop invariant i_0: i >= 0;

        loop invariant i_1: c >= 0;


        loop assigns i;
        loop assigns c;
    */
    while (i < 1000) {
        c = c + i;
        i = i + 1;
    }

    //@ assert  a_1: c >= 0;
}

