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
        loop invariant i_0: x == y;

        loop invariant i_14: x >= 0;

        loop invariant i_18: x == y && x <= n && x >= 0 && y >= 0;

        loop invariant i_19: x <= n && x >= 0 && y <= n && y >= 0;

        loop invariant i_20: x >= 0 && y >= 0;

        loop invariant i_21: x >= 0 && y >= 0 && x <= n && y <= n;

        loop invariant i_22: x <= n && x >= 0 && y >= 0 && y <= n;

        loop invariant i_23: x == y && x <= n && x >= 0 && y >= 0 && y <= n;

        loop invariant i_25: x >= 0 && x <= n;

        loop invariant i_26: y >= 0 && y <= n;

        loop invariant i_28: x == y && x >= 0 && x <= n && y >= 0 && y <= n;

        loop invariant i_30: x <= n && y <= n && x >= 0 && y >= 0;


        loop assigns y;
        loop assigns x;
    */
    while(unknown()) {
        x++;
        y++;
    }
    // Loop B
    /*@
        loop invariant i_2: x == y;

        loop invariant i_3: x == y && x <= n;

        loop invariant i_4: 0 < x || x == n;

        loop invariant i_5: x <= n && x == y;

        loop invariant i_12: x <= n;

        loop invariant i_13: x >= 0;

        loop invariant i_24: x >= 0 && x <= n;

        loop invariant i_27: y >= 0 && y <= n;


        loop assigns y;
        loop assigns x;
    */
    while(x!=n) {
        x--;
        y--;
    }

    //@ assert  a_1: y==n;
}
