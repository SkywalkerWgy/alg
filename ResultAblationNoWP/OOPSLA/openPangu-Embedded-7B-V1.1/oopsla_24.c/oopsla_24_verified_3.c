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
        loop invariant i_23: 0 <= i && i < n;

        loop invariant i_24: 0 <= j && j >= i;

        loop invariant i_25: 0 <= k && k < n;

        loop invariant i_26: 0 <= j && j < n;

        loop invariant i_27: 0 <= k && k >= j;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_34: 0 <= i && i < n;

            loop invariant i_35: 0 <= j && j >= i;

            loop invariant i_36: 0 <= k && k < n;

            loop invariant i_37: 0 <= j && j < n;

            loop invariant i_38: 0 <= k && k >= j;

            loop invariant i_39: k == j && j == i && 0 <= k && k < n;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_28: 0 <= i && i < n;

                loop invariant i_29: 0 <= j && j >= i;

                loop invariant i_30: 0 <= k && k < n;

                loop invariant i_31: 0 <= k && k >= j;

                loop invariant i_32: 0 <= j && j < n;

                loop invariant i_33: k == j && j == i && 0 <= k && k < n;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
