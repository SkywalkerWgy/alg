#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on "larg_const.c" from InvGen test suite  
 */
/*@
    requires n > 0;
    requires n < 10;
*/
void oopsla_21(int n) {
    int c1 = 4000;
    int c2 = 2000;
    int v;
    int i, k, j;

    i = 0;
    k = 0;

    // Loop A
    /*@
        loop invariant i_3: i <= n;

        loop invariant i_4: k is a nonnegative integer;

        loop invariant i_5: v is 0 or 1;

        loop invariant i_6: (v == 0) implies (k == c1);

        loop invariant i_7: (v == 1) implies (k == c2);

        loop invariant i_8: 0 <= k;

        loop invariant i_9: k == 0 or k == c1 or k == c2;

        loop invariant i_10: (k == c1) implies (v == 0);

        loop invariant i_11: (k == c2) implies (v == 1);


        loop assigns i, v, k;
    */
    while( i < n ) {
        i++;

        if(unknown2() % 2 == 0) {
            v = 0;
        }
        else{ 
            v = 1;
        }

        if( v == 0 ){
            k += c1;
        }
        else{ 
            k += c2;
        }
    }

    //@ assert  a_1: k > n;
}

