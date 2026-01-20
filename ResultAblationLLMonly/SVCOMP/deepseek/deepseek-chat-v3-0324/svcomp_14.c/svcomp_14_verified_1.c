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

        loop invariant i_1: k == (i == 0 ? 0 : (v == 0 ? i * c1 : (v == 1 ? i * c2 : i * c3)));


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
        loop invariant i_2: 0 <= j <= n;

        loop invariant i_3: k == (n == 0 ? 0 : (v == 0 ? n * c1 : (v == 1 ? n * c2 : n * c3))) - j;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert k > 0;
        j++;
        k--;
    }

    return 0;
}