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
        loop invariant i_0: 0 <= n <= 2*k;

        loop invariant i_1: (n % 2 == 0) ==> (i == j);

        loop invariant i_2: (n % 2 == 1) ==> ((!b && i == j + 1) || (b && j == i + 1));

        loop invariant i_3: 0 <= n && n <= 2*k;

        loop invariant i_4: n % 2 == 0 ==> i == j;

        loop invariant i_5: n % 2 == 1 ==> ((!b && i == j + 1) || (b && j == i + 1));


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
