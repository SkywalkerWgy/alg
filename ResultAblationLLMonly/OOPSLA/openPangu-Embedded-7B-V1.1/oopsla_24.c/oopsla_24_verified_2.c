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
        loop invariant i_7: i <= j <= k <= n && i <= j <= k < n;

        loop invariant i_8: i <= j <= k < n;

        loop invariant i_9: i <= j <= k < n && j < n;

        loop invariant i_10: i <= j <= k < n && k >= i;

        loop invariant i_11: i <= j <= k < n && k == j + (n - i - 1);

        loop invariant i_12: i <= j <= k < n && k <= n - 1 && k >= i;

        loop invariant i_13: i <= j <= k < n && k == n - 1;

        loop invariant i_14: i <= j <= k < n && k == n - 1 && k >= i;

        loop invariant i_15: i <= j <= k < n && k == n - 1 && j <= n - 1;

        loop invariant i_16: i <= j <= k < n && k == n - 1 && j <= n - 1 && j >= i;

        loop invariant i_17: i <= j <= k < n && k == n - 1 && j >= i;

        loop invariant i_18: i <= j <= k < n && k == n - 1 && j >= i && j <= n - 1;

        loop invariant i_19: i <= j <= k < n && k == n - 1 && i <= j && j <= n - 1;

        loop invariant i_20: i <= j <= k < n && k == n - 1 && i <= j && j >= i;

        loop invariant i_21: i <= j <= k < n && k == n - 1 && j >= i && j <= n - 1 && i <= j;

        loop invariant i_22: i <= j <= k < n && k == n - 1 && i <= j && j >= i && j <= n - 1 && i <= j;

        loop invariant i_23: i <= j <= k < n && k == n - 1 && i <= j && j >= i && j <= n - 1;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_47: k >= i && k <= n;

            loop invariant i_48: \forall m; k == m && i <= m <= j && m >= i && m < n ==> k == m;

            loop invariant i_49: \forall m; k == n - 1 && i <= m && m < n ==> j == m;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_24: for the following loop. loop invariant k >= i && k <= n;

                loop invariant i_25: k >= i && k <= n;

                loop invariant i_26: i <= j <= k < n && k >= i;

                loop invariant i_27: j >= i && j < n;

                loop invariant i_28: i <= j <= k < n && k <= n - 1 && k >= i;

                loop invariant i_29: i <= j <= k < n && k == n - 1 && j >= i && j < n;

                loop invariant i_30: i <= j <= k < n && k == n - 1 && i <= j && j >= i && j < n;

                loop invariant i_31: i <= j <= k < n && k == n - 1 && j >= i && j < n && i <= j;

                loop invariant i_32: k >= i && k <= n - 1;

                loop invariant i_33: \exists\, m; k == m && i <= m <= j && m >= i && m < n;

                loop invariant i_34: \forall\, m; i <= m <= j && m >= i && m < n ==> k == m;

                loop invariant i_35: \exists\, m; k == m && j == m && m >= i && m < n;

                loop invariant i_36: \forall\, m; j == m && i <= m && m >= i && m < n ==> k == m;

                loop invariant i_37: \exists\, m; k == n - 1 && j == m && m >= i && m < n;

                loop invariant i_38: \forall\, m; k == n - 1 && j == m && m >= i && m < n ==> k == m;

                loop invariant i_39: \exists\, m; k == n - 1 && i <= m && m < n;

                loop invariant i_40: \forall\, m; k == n - 1 && i <= m && m < n ==> j == m;

                loop invariant i_41: \forall\, m; k == n - 1 && j == m && m >= i && m < n ==> i <= m && m < n;

                loop invariant i_42: \forall\, m; k == n - 1 && j == m && m >= i && m < n ==> j >= i && j < n;

                loop invariant i_43: \forall\, m; k == n - 1 && i <= m && m < n ==> m >= i && m < n;

                loop invariant i_44: \exists\, m; k == n - 1 && j <= m && m < n;

                loop invariant i_45: \forall\, m; k == n - 1 && j <= m && m < n ==> m >= i && m < n;

                loop invariant i_46: \exists\, m;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
