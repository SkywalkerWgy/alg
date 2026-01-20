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
        loop invariant i_6: i <= n;

        loop invariant i_7: k >= 0 && (v == 0 ? k + c1 : v == 1 ? k + c2 : k + c3);

        loop invariant i_8: i <= n && k >= 0 && (v == 0 ? k + c1 : v == 1 ? k + c2 : k + c3);

        loop invariant i_9: j >= 0 && j <= n;

        loop invariant i_10: k >= 1;


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
        loop invariant i_11: j <= n;

        loop invariant i_12: k >= 0 && (v == 0 ? k + c1 : v == 1 ? k + c2 : k + c3);

        loop invariant i_13: j <= n && k >= 0 && (v == 0 ? k + c1 : v == 1 ? k + c2 : k + c3);

        loop invariant i_14: j >= 0;

        loop invariant i_15: k >= 0;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert k > 0;
        j++;
        k--;
    }

    return 0;
}