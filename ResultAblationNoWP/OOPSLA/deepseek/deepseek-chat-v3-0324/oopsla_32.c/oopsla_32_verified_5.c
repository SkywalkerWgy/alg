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
        loop invariant i_15: ``` loop invariant b == (n % 2 == 0);

        loop invariant i_16: b == (n % 2 == 0);

        loop invariant i_17: i == j + (n % 2 == 0 ? 0 : 1);

        loop invariant i_18: n >= 0 && n <= 2*k;


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
