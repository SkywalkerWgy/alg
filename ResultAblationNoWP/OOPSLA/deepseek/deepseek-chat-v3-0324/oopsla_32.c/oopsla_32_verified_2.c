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
        loop invariant i_4: b ==> (i == j + 1);

        loop invariant i_5: !b ==> (i == j);

        loop invariant i_6: n % 2 == 0 ==> (i == j);

        loop invariant i_7: n % 2 == 1 ==> (i == j + 1);


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
