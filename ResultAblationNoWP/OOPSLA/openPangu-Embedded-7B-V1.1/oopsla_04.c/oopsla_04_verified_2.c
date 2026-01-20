#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Taken from Gulwani PLDI'08:
 * Program Analysis as Constraint Solving
 */

void oopsla_04() {
    int x, y;

    x = -50;
    
    // Loop A
    /*@
        loop invariant i_1: x + y >= -50;

        loop invariant i_2: x < 0 && y > 0;

        loop invariant i_3: for the following loop. loop assigns y;

        loop invariant i_4: `x < 0 && y > 0` ensures that both `x` remains negative and `y` remains positive throughout the loop. The invariant `x + y >= -50` is also maintained because `x` starts at `-50` and both `x` and `y` are incremented by `y` in each iteration. The invariant holds for both the zero-iteration (when `x` is exactly 0) and normal termination cases. Since the postcondition `y > 0` is not provided, the loop invariant ensures that the loop will terminate with `y > 0` as required by the postcondition. Therefore, the loop invariant `x < 0 && y > 0` ensures the correctness of the loop termination condition.;

        loop invariant i_5: ensures that the loop will terminate with `y > 0` as required by the postcondition. Therefore, the loop invariant `x < 0 && y > 0` ensures the correctness of the loop termination condition.;

        loop invariant i_6: `x < 0 && y > 0` ensures the correctness of the loop termination condition.;


        loop assigns y;
        loop assigns x;
    */
    while( x < 0 ) {
        x = x + y;
        y++;
    }
    //@ assert a_1: y > 0;
}

