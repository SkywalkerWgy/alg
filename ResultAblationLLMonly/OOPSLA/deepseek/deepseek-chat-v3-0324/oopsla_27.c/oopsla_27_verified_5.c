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

        loop invariant i_8: s for the hinted Loop A: ``` loop invariant 1 <= k <= n;

        loop invariant i_9: k == 1 ==> i == l;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_2: l <= i <= n;

            loop invariant i_3: \forall integer j; l <= j < i ==> j == i;

            loop invariant i_7: s for the hinted loop: ``` loop invariant i_2: l <= i <= n;

            loop invariant i_10: k == 1;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_4: l <= i <= n;

            loop invariant i_5: \forall integer j; l <= j < i ==> k == 1;

            loop invariant i_11: s for the hinted Loop C: ``` loop invariant l <= i <= n;

            loop invariant i_12: 1 <= k <= n;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
