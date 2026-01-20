#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * "nested5.c" from InvGen test suite
 */

void oopsla_24() {
    int i,j,k,n;
    
    // Loop A
    /*@
        loop invariant i_0: 0 <= i <= n;

        loop invariant i_1: \forall integer x; i <= x < n ==> x >= i;

        loop invariant i_2: \forall integer y; i <= y < n ==> y >= i;

        loop invariant i_3: \forall integer z; j <= z < n ==> z >= i;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_7: j >= i;

            loop invariant i_8: j <= n;

            loop invariant i_9: \forall integer z; j <= z < n ==> z >= i;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_4: k >= j;

                loop invariant i_5: k < n;

                loop invariant i_6: \forall integer x; j <= x <= k ==> x >= i;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
