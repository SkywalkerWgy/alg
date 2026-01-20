#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Taken from Gulwani PLDI'08:
 * Program Analysis as Constraint Solving
 */

void oopsla_04() {
    int x, y;

    x = -50;
    
    // Loop A
    /*@
        loop invariant i_0: y > 0;

        loop invariant i_1: x <= -50 + (y-1)*y/2;

        loop invariant i_2: x < 0;


        loop assigns y;
        loop assigns x;
    */
    while( x < 0 ) {
        x = x + y;
        y++;
    }
    //@ assert a_1: y > 0;
}

