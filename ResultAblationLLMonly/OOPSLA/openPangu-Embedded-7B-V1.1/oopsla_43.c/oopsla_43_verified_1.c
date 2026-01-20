#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on ex16 from NECLA Static Analysis Benchmarks
 */

void oopsla_43(int x, int y){
    int i=0;
    int t=y;
    
    if (x==y) return;
    
    // Loop A
    /*@
        loop invariant i_0: t <= y;

        loop invariant i_1: t <= y && x >= 0;

        loop invariant i_2: x >= 0 && y >= t;


        loop assigns y, x, t, i;
    */
    while (unknown1()){
        if (x > 0)   
        y = y + x;
    }
    
    //@ assert a_1: y >= t;
}


