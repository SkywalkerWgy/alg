#include <assert.h>
int unknown1();

/*
 * "nest-if8" from InvGen benchmark suite
 */

/*@
    requires m + 1 < n;
*/
void oopsla_31(int i, int j, int k, int n, int m) {
    // Loop A
    /*@
        loop invariant i_22: i in [0, n); loop invariant j in [i, m); loop invariant k == j || k >= j; loop invariant j == j+2 || k == 0; loop invariant k < j || j < m; [Loop <Loop B>] loop invariant j >= 0; loop invariant k >= 0; [Loop <Loop C>] loop invariant k <= j; loop invariant j <= j + k; ```;

        loop invariant i_23: j in [i, m); loop invariant k == j || k >= j; loop invariant j == j+2 || k == 0; loop invariant k < j || j < m; [Loop <Loop B>] loop invariant j >= 0; loop invariant k >= 0; [Loop <Loop C>] loop invariant k <= j; loop invariant j <= j + k; ```;

        loop invariant i_24: k == j || k >= j;

        loop invariant i_25: j == j+2 || k == 0;

        loop invariant i_26: k < j || j < m;

        loop invariant i_27: j >= 0;

        loop invariant i_28: k >= 0;

        loop invariant i_29: k <= j;

        loop invariant i_30: j <= j + k;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_40: j in [i, m); loop invariant k == j || k >= j; loop invariant j == j+2 || k == 0; loop invariant k < j || j < m; [Loop <Loop B>] loop invariant j >= 0; loop invariant k >= 0; [Loop <Loop C>] loop invariant k <= j; loop invariant j <= j + k; loop invariant i_24: k == j || k >= j; loop invariant i_25: k == j || k >= j; loop invariant i_26: k < j || j < m; loop invariant i_27: j >= 0; loop invariant i_28: k >= 0; loop invariant i_29: k <= j; loop invariant i_30: j <= j + k; loop invariant i_31: j in [i, m); loop invariant i_32: k == j || k >= j; loop invariant i_33: j == j+2 || k == 0; loop invariant i_34: k < j || j < m; loop invariant i_35: k >= 0; loop invariant i_36: j >= 0; loop invariant i_37: k <= j; loop invariant i_38: j <= j + k; ```;

            loop invariant i_41: k == j || k >= j;

            loop invariant i_42: j == j+2 || k == 0;

            loop invariant i_43: k < j || j < m;

            loop invariant i_44: j >= 0;

            loop invariant i_45: k >= 0;

            loop invariant i_46: k <= j;

            loop invariant i_47: j <= j + k;

            loop invariant i_48: j in [i, m); loop invariant i_32: k == j || k >= j; loop invariant i_33: j == j+2 || k == 0; loop invariant i_34: k < j || j < m; loop invariant i_35: k >= 0; loop invariant i_36: j >= 0; loop invariant i_37: k <= j; loop invariant i_38: j <= j + k; ```;


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_31: i in [0, n); loop invariant j in [i, m); loop invariant k == j || k >= j; loop invariant j == j+2 || k == 0; loop invariant k < j || j < m; [Loop <Loop B>] loop invariant j >= 0; loop invariant k >= 0; [Loop <Loop C>] loop invariant k <= j; loop invariant j <= j + k; loop invariant i_24: k == j || k >= j; ```;

                    loop invariant i_32: j in [i, m); loop invariant k == j || k >= j; loop invariant j == j+2 || k == 0; loop invariant k < j || j < m; [Loop <Loop B>] loop invariant j >= 0; loop invariant k >= 0; [Loop <Loop C>] loop invariant k <= j; loop invariant j <= j + k; loop invariant i_24: k == j || k >= j; ```;

                    loop invariant i_33: k == j || k >= j;

                    loop invariant i_34: j == j+2 || k == 0;

                    loop invariant i_35: k < j || j < m;

                    loop invariant i_36: j >= 0;

                    loop invariant i_37: k >= 0;

                    loop invariant i_38: k <= j;

                    loop invariant i_39: j <= j + k;


                    loop assigns k;
                */
                while (k < j) {
                    k++;
                }
            } else {
                //@ assert  a_1: n + j + 5 > i;
                j += 2;
            }
        }
    }
}
