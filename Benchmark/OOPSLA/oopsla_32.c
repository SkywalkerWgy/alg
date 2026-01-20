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
  
    /*@
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
