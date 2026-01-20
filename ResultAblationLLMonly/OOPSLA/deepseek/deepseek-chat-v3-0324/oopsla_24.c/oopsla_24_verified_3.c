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

        loop invariant i_1: \forall integer j; i <= j < n ==> j >= i;

        loop invariant i_2: \forall integer j, k; i <= j < n && j <= k < n ==> k >= i;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_3: i <= j <= n;

            loop invariant i_4: \forall integer k; j <= k < n ==> k >= i;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_5: j <= k <= n;

                loop invariant i_6: \forall integer l; k <= l < n ==> l >= i;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
