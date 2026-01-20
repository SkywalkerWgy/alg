#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Adapted from ex17.c in NECLA test suite
 */
/*@
    requires flag > 0;
*/
void oopsla_18(int flag, int a) {
    int b;
    int j = 0;
    // Loop A
    /*@
        loop invariant i_0: j >= 0 && j <= 100;

        loop invariant i_1: flag == flag;

        loop invariant i_2: b == 100 || !flag;


        loop assigns j;
        loop assigns flag;
        loop assigns b;
    */
    for (b = 0; b < 100 ; ++b){
        if (flag)
            j = j + 1;
    }
    
    //@ assert  a_1: flag ==> j == 100;
}
