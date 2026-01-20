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
*/
void oopsla_37(int n) {
    int x = 0;
    int m = 0;
    // Loop A
    /*@
        loop invariant i_0: x >= 0;

        loop invariant i_1: m < n;

        loop invariant i_4: m >= 0;

        loop invariant i_6: x <= n;

        loop invariant i_10: x != n;

        loop invariant i_11: x < n && x >= 0 && x != n;

        loop invariant i_12: m >= 0 && m < n;

        loop invariant i_13: x <= n && x < n && x != n && m < n && m >= 0;


        loop assigns x;
        loop assigns m;
    */
    while (x < n) {
        if (unknown1()) {
        m = x;
        }
        x = x + 1;
    }

    //@ assert  a_1: n > 0 ==> 0 <= m && m < n;
    
}