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
        loop invariant i_21: 1 <= k <= n;

        loop invariant i_22: \forall integer m; l <= m < n ==> i == l || i > m;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_28: l <= i <= n;

            loop invariant i_29: \forall integer m; l <= m < i ==> k == \at(k, Pre);

            loop invariant i_30: i == l || \forall integer m; l <= m < n ==> i > m;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_23: s for Loop C: ``` loop invariant l <= i <= n;

            loop invariant i_24: l <= i <= n;

            loop invariant i_25: k == \at(k, Pre);

            loop invariant i_26: \forall integer m; l <= m < i ==> k == \at(k, Pre);

            loop invariant i_27: i == l || \forall integer m; l <= m < n ==> i > m;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
