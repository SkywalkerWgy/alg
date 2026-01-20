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
        loop invariant i_0: b == (n % 2 == 1);

        loop invariant i_3: b == (n % 2 == 1) || n == 0;

        loop invariant i_4: n == 0 ==> b == (n % 2 == 1);

        loop invariant i_5: n > 0 ==> b == (n % 2 == 1);

        loop invariant i_6: n == 0 ==> b == 0;


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
