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
        loop invariant i_5: 0 <= i && i < n;

        loop invariant i_6: 0 <= j && j >= i;

        loop invariant i_7: 0 <= k && k < n;

        loop invariant i_8: k == j && j == i && i >= 0;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_9: 0 <= j && j < n;

            loop invariant i_10: 0 <= k && k >= j;

            loop invariant i_18: 0 <= i && i < n;

            loop invariant i_19: 0 <= j && j >= i;

            loop invariant i_20: 0 <= k && k < n;

            loop invariant i_21: k == j && j == i && i >= 0;

            loop invariant i_22: k >= i && k < n && k == j && j == i && i >= 0;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_11: 0 <= k && k < n;

                loop invariant i_12: k == j && j >= i && i >= 0;

                loop invariant i_13: k >= i && k < n && k == j && j == i;

                loop invariant i_14: 0 <= j && j < n;

                loop invariant i_15: 0 <= k && k >= j;

                loop invariant i_16: k == j && j == i && i >= 0;

                loop invariant i_17: k >= i && k < n && k == j && j == i && i >= 0;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
