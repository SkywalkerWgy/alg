#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From CAV'12 by Sharma et al.
 */

/*@
    requires x == 0;
    requires y == 0;
    requires n == 0;
    ensures e_1: y == n;
*/
void oopsla_28(int x, int y, int n) {

    /*@
        loop assigns y, x;
    */
    while (unknown1()) {
        x++;
        y++;
    }

    /*@
        loop assigns y, x;
    */
    while (x != n) {
        x--;
        y--;
    }
}
