#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();


/*
 * From CAV'12 by Sharma et al.
 */

void oopsla_28() {
    int x = 0;
    int y = 0;
    int n = 0;
    // Loop A
    /*@
        loop invariant i_13: x == y;

        loop invariant i_14: x >= 0;

        loop invariant i_15: y >= 0;


        loop assigns y;
        loop assigns x;
    */
    while(unknown()) {
        x++;
        y++;
    }
    // Loop B
    /*@
        loop invariant i_16: x == y;

        loop invariant i_17: y == n + x_old - x;

        loop invariant i_18: x >= 0;

        loop invariant i_19: y >= 0;


        loop assigns y;
        loop assigns x;
    */
    while(x!=n) {
        x--;
        y--;
    }

    //@ assert  a_1: y==n;
}
