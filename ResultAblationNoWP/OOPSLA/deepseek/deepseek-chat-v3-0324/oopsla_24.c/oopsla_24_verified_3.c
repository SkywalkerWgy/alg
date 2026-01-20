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
        loop invariant i_16: 0 <= i <= n;

        loop invariant i_17: \forall integer k1; i <= k1 < n ==> k1 >= i;

        loop invariant i_18: j == i;

        loop invariant i_19: k == j;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_23: i <= j <= n;

            loop invariant i_24: k == j;

            loop invariant i_25: \forall integer k1; i <= k1 < j ==> k1 >= i;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_20: k >= j;

                loop invariant i_21: k <= n;

                loop invariant i_22: \forall integer p; j <= p < k ==> p >= i;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
