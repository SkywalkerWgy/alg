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
        loop invariant i_4: j >= i;

        loop invariant i_5: i >= 1 && j >= i;

        loop invariant i_6: i <= 9 && j >= i;

        loop invariant i_7: i <= 9;

        loop invariant i_8: i >= 1 && j >= i && i <= 9;

        loop invariant i_9: j >= i && j <= 10;

        loop invariant i_10: i >= 1 && i <= 9;

        loop invariant i_11: j >= 6;


        loop assigns i, j;
    */
    while (j >= i) {
        i = i + 2;
        j = -1 + j;
    }
    //@ assert j == 6;
    return 0;
}