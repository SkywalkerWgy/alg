#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From "Simplifying Loop Invariant Generation using Splitter Predicates", Sharma et al. CAV'11
 */

/*@
    requires n >= 0;
    requires m >= 0;
    requires m < n;
    ensures  e_1: y == n;
*/
void oopsla_19(int n, int m, int x, int y) {

    /*@
        loop assigns y, x;
    */
    while (x < n) {
        x++;
        if (x > m) y++;
    }
}
