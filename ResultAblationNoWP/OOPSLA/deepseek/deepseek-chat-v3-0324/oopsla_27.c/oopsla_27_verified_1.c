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
        loop invariant i_0: s for Loop A: ``` loop invariant 1 <= k <= n;

        loop invariant i_1: 1 <= k <= n;

        loop invariant i_2: \forall integer m; 1 <= m < k ==> (i == l || i >= n);

        loop invariant i_3: l > 0;


        loop assigns k, i;
    */
    for (k = 1; k < n; k++) {

        // Loop B
        /*@
            loop invariant i_8: l <= i <= n;

            loop invariant i_9: \forall integer m; 1 <= m < k ==> (i == l || i >= n);

            loop invariant i_10: l > 0;


            loop assigns i;
        */
        for (i = l; i < n; i++) {

        }

        // Loop C
        /*@
            loop invariant i_4: 1 <= k <= n;

            loop invariant i_5: l <= i <= n;

            loop invariant i_6: \forall integer m; 1 <= m < k ==> (i == l || i >= n);

            loop invariant i_7: l > 0;


            loop assigns k, i;
        */
        for (i = l; i < n; i++) {
            //@ assert  a_1: 1 <= k;
        }
    }
}
