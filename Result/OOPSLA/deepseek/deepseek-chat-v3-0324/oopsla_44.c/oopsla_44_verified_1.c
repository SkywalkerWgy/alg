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

        loop invariant i_1: i <= k + 1;


        loop assigns j;
        loop assigns i;
    */
    while ( i <= k) {
        i++;
        j = j + n;
    }

    //@ assert  a_1: flag == 1 ==> j == i;
}


