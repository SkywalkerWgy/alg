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
        loop invariant i_35: 0 <= i <= n;

        loop invariant i_36: \forall integer x; i <= x < n ==> x >= i;

        loop invariant i_37: \forall integer y; i <= y < n ==> y >= i;

        loop invariant i_38: \forall integer z; j <= z < n ==> z >= i;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_41: s for Loop B: ``` loop invariant i <= j <= n;

            loop invariant i_42: i <= j <= n;

            loop invariant i_43: \forall integer z; j <= z < n ==> z >= i;

            loop invariant i_44: \forall integer y; i <= y < n ==> y >= i;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_39: i <= k <= n;

                loop invariant i_40: \forall integer p; j <= p < k ==> p >= i;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
