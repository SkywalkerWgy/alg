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

        loop invariant i_1: x >= 0;

        loop invariant i_2: y >= 0;


        loop assigns y;
        loop assigns x;
    */
    while(unknown()) {
        x++;
        y++;
    }
    // Loop B
    /*@
        loop invariant i_3: s for the second loop: ``` loop invariant x == y;

        loop invariant i_4: x == y;

        loop invariant i_5: y == n - (x0 - x);

        loop invariant i_6: x >= 0;

        loop invariant i_7: y >= 0;


        loop assigns y;
        loop assigns x;
    */
    while(x!=n) {
        x--;
        y--;
    }

    //@ assert  a_1: y==n;
}
