#include <assert.h>
/*@
ensures \result >= 0;
*/
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Adapted from "Automated Error Diagnosis Using Abductive Inference" by Dillig et al.
 */
/*@
requires n > 0;
*/
void oopsla_41(int n, int flag) {
    int k = 1;
    if (flag) {
        k = unknown1();
    }
    int i = 0, j = 0;
    // Loop A
    /*@
        loop invariant i_3: i <= n;

        loop invariant i_4: j == \sum_{m=1}^i m;

        loop invariant i_5: k >= 0 && k == \sum_{m=1}^i m;

        loop invariant i_6: z <= 2 * n + k;

        loop invariant i_7: z > 2 * n && k == unknown1();

        loop invariant i_8: \exists integer k; k >= 0 && k <= n && j == \sum_{m=1}^i m;

        loop invariant i_9: \forall integer k; 0 <= k < i ==> k <= n;

        loop invariant i_10: \forall integer k; 0 <= k < i ==> j >= k;

        loop invariant i_11: \forall integer k; 0 <= k < i ==> j = \sum_{m=1}^i m;


        loop assigns j;
        loop assigns i;
    */
    while (i <= n) {
        i++;
        j += i;
    }
    int z = k + i + j;
    //@ assert  a_1: z > 2 * n;
}