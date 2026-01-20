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
        loop invariant i_7: x >= 0;

        loop invariant i_8: m < x;

        loop invariant i_9: for the following loop. loop assigns x;

        loop invariant i_10: for the provided code snippet, in ACSL, is: `loop invariant x >= 0 && m < x;

        loop invariant i_11: x >= 0 && m < x;


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