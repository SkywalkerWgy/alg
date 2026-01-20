#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Adapted from ex20 from NECLA Static Analysis Benchmarks
 */

void oopsla_44(int k, int flag){
    int i=0;
    int j=0;
    int n;

    if (flag == 1){
        n=1;
    } else {
        n=2;
    }

    i=0;

    // Loop A
    /*@
        loop invariant i_0: j == i * n;

        loop invariant i_2: i >= 0;

        loop invariant i_3: i <= k + 1 || flag == 2;

        loop invariant i_4: flag == 1 ==> i <= k + 1;

        loop invariant i_5: i <= k + 1 || flag != 1;

        loop invariant i_7: i <= k + 1 || (flag == 2 && n == 2);

        loop invariant i_8: i <= k || (flag == 2 && n == 2);


        loop assigns j;
        loop assigns i;
    */
    while ( i <= k) {
        i++;
        j = j + n;
    }

    //@ assert  a_1: flag == 1 ==> j == i;
}


