#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Taken from Gulwani PLDI'08:
 * Program Analysis as Constraint Solving
 */

/*@
    requires x == -50;
    ensures  e_1: y > 0;
*/
void oopsla_04(int x, int y) {
    /*@
        loop assigns y;
        loop assigns x;
    */
    while (x < 0) {
        x = x + y;
        y++;
    }
}
