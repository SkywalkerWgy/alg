#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * IC3 motivating example
 */

/*@
    requires x == 1;
    requires y == 1;
    ensures e_1: y >= 1;
*/
void oopsla_01(int x, int y) {
    /*@
        loop assigns x;
        loop assigns y;
    */
    while (unknown1()) {
        int t1 = x;
        int t2 = y;
        x = t1 + t2;
        y = t1 + t2;
    }
}