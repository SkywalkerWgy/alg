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
        loop invariant i_8: x == y;

        loop invariant i_9: x >= 0;


        loop assigns y;
        loop assigns x;
    */
    while(unknown()) {
        x++;
        y++;
    }
    // Loop B
    /*@
        loop invariant i_10: x == y;

        loop invariant i_11: x >= 0;

        loop invariant i_12: y - x == n - x;


        loop assigns y;
        loop assigns x;
    */
    while(x!=n) {
        x--;
        y--;
    }

    //@ assert  a_1: y==n;
}
