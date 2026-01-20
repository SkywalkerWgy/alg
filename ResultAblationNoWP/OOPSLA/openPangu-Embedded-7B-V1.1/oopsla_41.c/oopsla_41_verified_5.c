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
        loop invariant i_17: i <= n;

        loop invariant i_18: j == k + i;

        loop invariant i_19: k == 1;

        loop invariant i_20: flag == 0 || k == unknown1();

        loop invariant i_21: i == 0 || j == k + i;

        loop invariant i_22: z == k + i + j;


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