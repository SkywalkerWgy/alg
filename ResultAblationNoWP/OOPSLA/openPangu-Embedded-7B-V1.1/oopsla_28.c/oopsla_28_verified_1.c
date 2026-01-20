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

        loop invariant i_1: 0 <= x && 0 <= y;

        loop invariant i_2: x >= 0 && y >= x;

        loop invariant i_3: x <= y && x != n && y != unknown1();

        loop invariant i_4: y == n && x != unknown1();

        loop invariant i_5: y >= x && y <= unknown4();

        loop invariant i_6: \exists integer k; 0 <= k < 10 && x == y && y <= n;


        loop assigns y;
        loop assigns x;
    */
    while(unknown()) {
        x++;
        y++;
    }
    // Loop B
    /*@
        loop invariant i_7: x == y;

        loop invariant i_8: x <= n && y >= 0;

        loop invariant i_9: y >= x && y <= n;

        loop invariant i_10: x != unknown1();

        loop invariant i_11: y != unknown1();

        loop invariant i_12: \exists integer k; 0 <= k < 10 && x == y && y <= n;

        loop invariant i_13: x >= 0 && y >= x;

        loop invariant i_14: x <= y && y <= n;

        loop invariant i_15: y == n && x != unknown1();

        loop invariant i_16: y >= x && y <= unknown4();


        loop assigns y;
        loop assigns x;
    */
    while(x!=n) {
        x--;
        y--;
    }

    //@ assert  a_1: y==n;
}
