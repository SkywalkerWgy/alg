#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on "SYNERGY: A New Algorithm for Property Checking" by Gulavani et al.
 */

/*@
    requires i == 0;
    requires c == 0;
    ensures  e_1: c >= 0;
*/
void oopsla_30(int i, int c) {

    /*@
        loop assigns i, c;
    */
    while (i < 1000) {
        c = c + i;
        i = i + 1;
    }
}
