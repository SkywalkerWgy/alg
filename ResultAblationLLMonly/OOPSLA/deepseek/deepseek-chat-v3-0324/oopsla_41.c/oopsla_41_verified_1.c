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
        loop invariant i_0: j == (i * (i + 1)) / 2;

        loop invariant i_1: 0 <= i <= n + 1;


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