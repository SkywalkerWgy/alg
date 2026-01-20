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
        loop invariant i_0: 1 <= k <= n;

        loop invariant i_1: \forall integer j; l <= j < n ==> i == j;

        loop invariant i_6: l <= i <= n;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_2: l <= i <= n;

            loop invariant i_3: \forall integer j; l <= j < i ==> j == i;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_4: l <= i <= n;

            loop invariant i_5: \forall integer j; l <= j < i ==> k == 1;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
