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
        loop invariant i_15: y >= x;

        loop invariant i_16: y <= x + n;


        loop assigns y;
        loop assigns x;
    */
    while(unknown()) {
        x++;
        y++;
    }
    // Loop B
    /*@
        loop invariant i_17: y >= x;

        loop invariant i_18: y <= x + n;

        loop invariant i_19: for the following loop. loop assigns y;

        loop invariant i_20: x <= n;


        loop assigns y;
        loop assigns x;
    */
    while(x!=n) {
        x--;
        y--;
    }

    //@ assert  a_1: y==n;
}
