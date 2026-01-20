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
        loop invariant i_9: x == y;

        loop invariant i_10: x >= 0 && y >= 0;

        loop invariant i_11: `x == y` implies that both `x` and `y` are either zero or non-zero together. However, if `x` and `y` can differ within the loop (e.g., `x` and `y` are unrelated variables), this invariant would not hold. The invariant `x == y` must be refined or removed if `x` and `y` are not supposed to be equal in the loop. If `x` and `y` are supposed to be unrelated but both must decrease together (e.g., as counters), a stronger invariant like `x >= y` could be considered instead. ### Explanation: - The loop invariant `x == y` directly reflects the hint's instruction to infer the invariant based on `loop assigns x;

        loop invariant i_12: `x == y` directly reflects the hint's instruction to infer the invariant based on `loop assigns x;

        loop invariant i_13: x != y;

        loop invariant i_14: x == y && x != 0;

        loop invariant i_15: x >= y;


        loop assigns y;
        loop assigns x;
    */
    while(x != 0) {
        x--;
        y--;
    }

    //@ assert  a_1: i == j ==> y == 0;
}

