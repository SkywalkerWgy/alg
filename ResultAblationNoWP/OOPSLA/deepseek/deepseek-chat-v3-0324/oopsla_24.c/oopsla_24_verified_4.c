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
        loop invariant i_26: 0 <= i <= n;

        loop invariant i_27: \forall integer x; i <= x < n ==> x >= i;

        loop invariant i_28: \forall integer y; i <= y < n ==> y >= i;

        loop invariant i_29: \forall integer z; j <= z < n ==> z >= j;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_32: i <= j <= n;

            loop invariant i_33: \forall integer y; i <= y < j ==> y >= i;

            loop invariant i_34: \forall integer z; j <= z < n ==> z >= j;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_30: j <= k <= n;

                loop invariant i_31: \forall integer x; j <= x < k ==> x >= i;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
