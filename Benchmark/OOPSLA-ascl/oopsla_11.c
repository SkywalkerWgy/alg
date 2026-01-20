#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on ex3 from NECLA Static Analysis Benchmarks
 */

/*@
    requires j == 0;
    requires x == 100;
    ensures  e_1: j == 2*x;
    assigns \nothing;
*/
void oopsla_11(int j, int i, int x){

    /*@
        loop invariant x == 100;
        loop invariant j == 2*i;
        loop invariant i <= x;
        loop assigns j, i;
    */
    for (i = 0; i < x; i++) {
        j = j + 2;
    }
    //@ assert j == 2*x;
}
