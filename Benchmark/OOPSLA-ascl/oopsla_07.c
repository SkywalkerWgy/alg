#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From "Path Invariants" PLDI 07 by Beyer et al.
*/

/*@
    requires n > 0;
    requires i == 0;
    requires a == 0;
    requires b == 0;
    ensures e_1: a + b == 3 * n; 
*/
void oopsla_07(int n, int i, int a, int b) {
    /*@
        loop assigns i, b, a;
    */
    while (i < n) {
        if (unknown1()) {
            a = a + 1;
            b = b + 2;
        } else {
            a = a + 2;
            b = b + 1;
        }
        i = i + 1;
    }
}
