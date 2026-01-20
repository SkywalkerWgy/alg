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

        loop invariant i_7: s for Loop A: ``` loop invariant 0 <= i <= n;

        loop invariant i_9: s for each loop in ACSL format: For Loop A: ``` loop invariant 0 <= i <= n;

        loop invariant i_10: i <= j <= n;

        loop invariant i_11: \forall integer k; j <= k < n ==> k >= i;

        loop invariant i_12: j <= k <= n;

        loop invariant i_13: \forall integer l; k <= l < n ==> l >= i;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_3: i <= j <= n;

            loop invariant i_4: \forall integer k; j <= k < n ==> k >= i;

            loop invariant i_8: s for Loop B: ``` loop invariant i <= j <= n;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_5: j <= k <= n;

                loop invariant i_6: \forall integer l; k <= l < n ==> l >= i;

                loop invariant i_14: s for Loop C: ``` loop invariant j <= k <= n;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
