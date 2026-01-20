// Source: Michael Colon, Sriram Sankaranarayanan, Henny Sipma: "Linear
// Invariant Generation using Non-Linear Constraint Solving", CAV 2003.
#include "assert.h"
# define LARGE_INT 1000000

/*@ 
requires 0 <= k && k <= 1;
*/
int svcomp_7(int k) {
    int i,j;
    i = 1;
    j = 1;
    // Loop A
    /*@
        loop invariant i_0: 0 <= k && k <= 1;

        loop invariant i_1: 1 <= i;

        loop invariant i_2: j == i;

        loop invariant i_3: i + k == 2;


        loop assigns k;
        loop assigns j;
        loop assigns i;
    */
    while (i < LARGE_INT) {
        i = i + 1;
        j = j + k;
        k = k - 1;
        //@ assert 1 <= i + k && i + k <= 2 && i >= 1;
    }
    return 0;
}