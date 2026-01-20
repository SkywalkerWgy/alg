#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * ex49 from NECLA Static Analysis Benchmarks
 */

/*@
    requires n >= 0;
*/
void oopsla_23(int n) {
    int i, sum = 0;

    // Loop A
    /*@
        loop invariant i_5: i >= 0 && i < n;

        loop invariant i_6: sum >= 0;

        loop invariant i_7: sum == i * (i - 1);


        loop assigns sum;
        loop assigns i;
    */
    for (i = 0; i < n; ++i){
        sum = sum + i;
    }

    //@ assert a_1: sum >= 0;
}