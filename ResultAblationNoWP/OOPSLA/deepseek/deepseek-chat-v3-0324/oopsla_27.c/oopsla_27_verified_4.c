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
        loop invariant i_31: 1 <= k <= n;

        loop invariant i_32: \forall integer j; l <= j < n ==> i == j || i == l;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_37: s for Loop B: ``` loop invariant l <= i <= n;

            loop invariant i_38: l <= i <= n;

            loop invariant i_39: \forall integer j; l <= j < i ==> i == j || i == l;

            loop invariant i_40: 1 <= k <= n;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_33: s for Loop C: ``` loop invariant l <= i <= n;

            loop invariant i_34: l <= i <= n;

            loop invariant i_35: 1 <= k <= n;

            loop invariant i_36: \forall integer j; l <= j < n ==> i == j || i == l;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
