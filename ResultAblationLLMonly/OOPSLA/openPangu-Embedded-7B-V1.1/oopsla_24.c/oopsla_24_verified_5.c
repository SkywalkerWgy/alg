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
        loop invariant i_91: 0 <= i < n;

        loop invariant i_92: 0 <= j < n && i <= j;

        loop invariant i_93: 0 <= k < n && j <= k && i <= k;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_110: 0 <= i < n;

            loop invariant i_111: 0 <= j < n && i <= j;

            loop invariant i_112: 0 <= k < n && j <= k && i <= k;

            loop invariant i_113: j >= i && j < n && k >= j && k < n;

            loop invariant i_114: n > 0;

            loop invariant i_115: k >= i;

            loop invariant i_116: k >= 0;

            loop invariant i_117: j < n;

            loop invariant i_118: k < n;

            loop invariant i_119: i < n;

            loop invariant i_120: j >= i;

            loop invariant i_121: k >= j;

            loop invariant i_122: i <= k;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_94: 0 <= i < n;

                loop invariant i_95: 0 <= j < n && i <= j;

                loop invariant i_96: 0 <= k < n && j <= k && i <= k;

                loop invariant i_97: j >= i && j < n && k >= j && k < n;

                loop invariant i_98: n > 0;

                loop invariant i_99: k >= i && k < n;

                loop invariant i_100: k < n && k >= j && k >= i;

                loop invariant i_101: i >= 0;

                loop invariant i_102: j >= 0;

                loop invariant i_103: k >= 0;

                loop invariant i_104: j < n;

                loop invariant i_105: k < n;

                loop invariant i_106: i < n;

                loop invariant i_107: j >= i;

                loop invariant i_108: k >= j;

                loop invariant i_109: i <= k;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
