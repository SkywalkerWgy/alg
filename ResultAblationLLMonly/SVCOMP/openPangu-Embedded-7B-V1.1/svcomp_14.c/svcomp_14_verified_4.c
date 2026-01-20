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
        loop invariant i_16: 0 <= i <= n;

        loop invariant i_17: k == i * c1 - (c1 + c2);

        loop invariant i_18: (v == 0 ? (k - c1) : (k - c2)) >= 0 && v < 2;

        loop invariant i_19: k == j * 2 && j <= n;

        loop invariant i_20: 0 <= j <= n;

        loop invariant i_21: ...;


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
        loop invariant i_22: k == j * 2 && k > 0;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert k > 0;
        j++;
        k--;
    }

    return 0;
}