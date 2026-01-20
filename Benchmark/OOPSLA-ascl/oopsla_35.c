#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * InvGen, CAV'09 paper, fig 2
 */

/*@
    requires n > 0;
    requires x == 0;
    ensures  e_1: n > 0 ==> x == n;
*/
void oopsla_35(int n, int x) {
    /*@
        loop assigns x;
    */
    while (x < n) {
        x++;
    }
}
