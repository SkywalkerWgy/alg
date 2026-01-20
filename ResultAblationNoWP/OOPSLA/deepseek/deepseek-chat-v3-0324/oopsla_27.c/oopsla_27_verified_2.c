#include <assert.h>

/*
 * "nested2.c" from InvGen benchmark suite
 */

/*@
    requires l > 0;
*/
void oopsla_27(int l, int i, int k, int n) {

    // Loop A
    /*@
        loop invariant i_11: 1 <= k <= n;

        loop invariant i_12: l <= i <= n;

        loop invariant i_13: \forall integer j; l <= j < i ==> j < n;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_17: s for Loop B: ``` loop invariant l <= i <= n;

            loop invariant i_18: l <= i <= n;

            loop invariant i_19: \forall integer j; l <= j < i ==> j < n;

            loop invariant i_20: k == \at(k, Pre);


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_14: l <= i <= n;

            loop invariant i_15: k == \at(k, Pre);

            loop invariant i_16: \forall integer j; l <= j < i ==> j < n;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
