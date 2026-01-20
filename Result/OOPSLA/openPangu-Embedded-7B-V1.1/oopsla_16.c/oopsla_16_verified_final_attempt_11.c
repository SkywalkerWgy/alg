#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();


/*
 * From "A Practical and Complete Approach to Predicate Refinement" by McMillan TACAS'06
 */

void oopsla_16(int i, int j) {
  
    int x = i;
    int y = j;
    
    // Loop A
    /*@
        loop invariant i_6: i >= j;

        loop invariant i_8: i == j;

        loop invariant i_9: x >= 0;

        loop invariant i_10: y >= 0;

        loop invariant i_11: x >= 0 && y >= 0 && i >= j;


        loop assigns y;
        loop assigns x;
    */
    while(x != 0) {
        x--;
        y--;
    }

    //@ assert  a_1: i == j ==> y == 0;
}

