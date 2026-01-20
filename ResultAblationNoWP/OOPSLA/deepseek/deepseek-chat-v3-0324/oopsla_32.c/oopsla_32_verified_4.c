#include <assert.h>

/*
 * "split.c" from InvGen benchmark suite
 */

void oopsla_32() {
    int k = 100;
    int b;
    int i;
    int j;
    int n;
    i = j;
  
    // Loop A
    /*@
        loop invariant i_11: ``` loop invariant b == (n % 2 == 1);

        loop invariant i_12: b == (n % 2 == 1);

        loop invariant i_13: i == j + (n % 2);

        loop invariant i_14: n >= 0 && n <= 2*k;


        loop assigns i, j, b;
    */
    for( n = 0 ; n < 2*k ; n++ ) {
        if(b) {
            i++;
        } 
        else {
            j++;
        }
        b = !b;
    }
    //@ assert a_1: (i == j);
}
