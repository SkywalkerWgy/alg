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
        loop invariant i_65: i + j + k < n;

        loop invariant i_66: j >= 0;

        loop invariant i_67: k >= 0;

        loop invariant i_68: for the following loop. loop assigns n, m, k, j, i;


        loop assigns n, m, k, j, i;
    */
    for (i = 0; i < n; i += 4) {

        // Loop B
        /*@
            loop invariant i_69: j >= i;

            loop invariant i_82: k == j;

            loop invariant i_83: i + j + k == n;

            loop invariant i_84: j >= 0;

            loop invariant i_85: k >= 0;

            loop invariant i_86: n - i >= 0;

            loop invariant i_87: m - j >= 0;

            loop invariant i_88: \exists integer idx; i <= idx < n && j <= idx && k == \at(idx, value);

            loop invariant i_89: \forall integer idx; \at(idx, value) == 0 && idx == k && i == \at(idx, value) && j == \at(idx, value) && k == \at(idx, value);

            loop invariant i_90: \forall integer idx; \at(idx, value) == 0 ==> \at(idx, value) == \at(idx, value) && \at(idx, value) == 0;

            loop invariant i_91: \forall integer idx; \at(idx, value) == \at(idx, value) && \at(idx, value) == 0 && \at(idx, value) == 0;

            loop invariant i_92: \forall integer idx; \at(idx, value) == \at(idx, value) && \at(idx, value) == \at(idx, value) && \at(idx, value) == 0;

            loop invariant i_93: \forall integer idx; \at(idx, value) == \at(idx, value) && \at(idx, value) == \at(idx, value) && \at(idx, value) == 0 && \at(idx, value) == \at(idx, value);


            loop assigns k, j;
        */
        for (j = i; j < m;) {
            if (unknown1()) {
                //@ assert j >= 0;
                j++;
                k = 0;

                // Loop C
                /*@
                    loop invariant i_70: k == j;

                    loop invariant i_71: i + j + k == n;

                    loop invariant i_72: j >= 0;

                    loop invariant i_73: k >= 0;

                    loop invariant i_74: n - i >= 0;

                    loop invariant i_75: m - j >= 0;

                    loop invariant i_76: \exists integer idx; i <= idx < n && j <= idx && k == \at(idx, value);

                    loop invariant i_77: \forall integer idx; \at(idx, value) == 0 && idx == k && i == \at(idx, value) && j == \at(idx, value) && k == \at(idx, value);

                    loop invariant i_78: \forall integer idx; \at(idx, value) == 0 ==> \at(idx, value) == \at(idx, value) && \at(idx, value) == 0;

                    loop invariant i_79: \forall integer idx; \at(idx, value) == \at(idx, value) && \at(idx, value) == 0 && \at(idx, value) == 0;

                    loop invariant i_80: \forall integer idx; \at(idx, value) == \at(idx, value) && \at(idx, value) == \at(idx, value) && \at(idx, value) == 0;

                    loop invariant i_81: \forall integer idx; \at(idx, value) == \at(idx, value) && \at(idx, value) == \at(idx, value) && \at(idx, value) == 0 && \at(idx, value) == \at(idx, value);


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
