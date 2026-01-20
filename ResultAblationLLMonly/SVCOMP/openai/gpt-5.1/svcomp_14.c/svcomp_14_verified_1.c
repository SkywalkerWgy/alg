#include "assert.h"

/*@
    requires 0 <= n && n < 10;
    requires 0 <= v && v < 2;
*/
int svcomp_14(int n, int v) {
    int c1 = 4000;
    int c2 = 2000;
    int c3 = 10000;

    int i, k, j;

    k = 0;
    i = 0;

    // Loop A
    /*@
        loop invariant i_0: 0 <= i <= n;

        loop invariant i_1: k >= 0;

        loop invariant i_2: v == 0 ==> k == i * c1;

        loop invariant i_3: v == 1 ==> k == i * c2;

        loop invariant i_4: v != 0 && v != 1 ==> k == i * c3;


        loop assigns i, k;
    */
    while(i < n) {
        i++;

        if( v == 0 )
            k += c1;
        else if( v == 1 )
            k += c2;
        else
            k += c3;
    }

    j = 0;
    
    // Loop B
    /*@
        loop invariant i_5: 0 <= j <= n;

        loop invariant i_6: k >= 0;

        loop invariant i_7: v == 0 ==> k + j == n * c1;

        loop invariant i_8: v == 1 ==> k + j == n * c2;

        loop invariant i_9: v != 0 && v != 1 ==> k + j == n * c3;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert k > 0;
        j++;
        k--;
    }

    return 0;
}