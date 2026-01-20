// Source: A. Costan, S. Gaubert, E. Goubault, M. Martel, S. Putot: "A Policy
// Iteration Algorithm for Computing Fixed Points in Static Analysis of
// Programs", CAV 2005

#include "assert.h"

int svcomp_5() {
    int i,j;
    i = 1;
    j = 10;
    
    // Loop A
    /*@
        loop invariant i_8: i + j >= 1;


        loop assigns i, j;
    */
    while (j >= i) {
        i = i + 2;
        j = -1 + j;
    }
    //@ assert j == 6;
    return 0;
}