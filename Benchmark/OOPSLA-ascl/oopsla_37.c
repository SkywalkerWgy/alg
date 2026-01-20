#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Taken from "Counterexample Driven Refinement for Abstract Interpretation" (TACAS'06) by Gulavani
 */

/*@
    requires n > 0;
    ensures  e_1: n > 0 ==> (0 <= m && m < n);
*/
void oopsla_37(int n, int x, int m) {
    x = 0;
    m = 0;
    /*@
        loop assigns x, m;
    */
    while (x < n) {
        if (unknown1()) {
            m = x;
        }
        x = x + 1;
    }
}
