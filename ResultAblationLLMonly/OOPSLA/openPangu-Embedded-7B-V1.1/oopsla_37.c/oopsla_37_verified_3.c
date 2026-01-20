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
        loop invariant i_6: 0 <= x && x < n;


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