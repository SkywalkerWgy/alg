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
        loop invariant i_1: i >= 0;

        loop invariant i_2: i < n;

        loop invariant i_3: sum >= 0;

        loop invariant i_4: for the following loop. loop assigns sum;

        loop invariant i_5: in the code is: - `i >= 0` (ensuring the loop index remains non-negative). - `i < n` (ensuring the loop index does not exceed the input size). - `sum >= 0` (ensuring the accumulated sum remains non-negative). These invariants ensure the loop runs correctly and maintains the expected properties.;


        loop assigns sum;
        loop assigns i;
    */
    for (i = 0; i < n; ++i){
        sum = sum + i;
    }

    //@ assert a_1: sum >= 0;
}