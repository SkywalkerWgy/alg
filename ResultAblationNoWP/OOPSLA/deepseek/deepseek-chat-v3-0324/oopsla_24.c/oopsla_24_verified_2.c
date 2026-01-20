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
        loop invariant i_10: 0 <= i <= n;

        loop invariant i_11: \forall integer k_outer; 0 <= k_outer < i ==> (\forall integer k_inner; k_outer <= k_inner < n ==> k_inner >= k_outer); ```;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_14: i <= j <= n;

            loop invariant i_15: \forall integer m; i <= m < j ==> m >= i;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_12: j <= k <= n;

                loop invariant i_13: \forall integer m; j <= m < k ==> m >= i;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
