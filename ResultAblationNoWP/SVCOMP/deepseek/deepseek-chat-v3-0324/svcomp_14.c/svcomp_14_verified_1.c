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

        loop invariant i_1: k == (v == 0 ? c1 * i : (v == 1 ? c2 * i : c3 * i));

        loop invariant i_2: v == 0 || v == 1 || v == 2;


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
        loop invariant i_3: 0 <= j <= n;

        loop invariant i_4: k == (v == 0 ? c1 * n - j : (v == 1 ? c2 * n - j : c3 * n - j));

        loop invariant i_5: k > 0 || j == n;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert k > 0;
        j++;
        k--;
    }

    return 0;
}