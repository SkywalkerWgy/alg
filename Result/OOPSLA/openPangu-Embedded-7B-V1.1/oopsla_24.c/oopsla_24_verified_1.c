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
        loop invariant i_0: i >= 0 && i < n;

        loop invariant i_1: j >= i && j < n;

        loop invariant i_2: k >= j && k < n;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_8: i >= 0 && i < n;

            loop invariant i_9: j >= i && j < n;

            loop invariant i_10: k >= j && k < n;

            loop invariant i_11: ", "precondition": "i >= 0 && i < n", "postcondition": "i >= 0 && i < n" }, { "invariant": "j >= i && j < n", "type": "loop invariant", "precondition": "j >= i && j < n", "postcondition": "j >= i && j < n" }, { "invariant": "k >= j && k < n", "type": "loop invariant", "precondition": "j >= i && k >= j && k < n", "postcondition": "k >= j && k < n" } ] } ```;

            loop invariant i_12: ", "precondition": "j >= i && j < n", "postcondition": "j >= i && j < n" }, { "invariant": "k >= j && k < n", "type": "loop invariant", "precondition": "j >= i && k >= j && k < n", "postcondition": "k >= j && k < n" } ] } ```;

            loop invariant i_13: ", "precondition": "j >= i && k >= j && k < n", "postcondition": "k >= j && k < n" } ] } ```;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_3: i >= 0 && i < n;

                loop invariant i_4: j >= i && j < n;

                loop invariant i_5: k >= j && k < n;

                loop invariant i_6: clauses in C-style comments, but the output must be in JSON format as per the system rules.", "message": "Please provide the loop invariants in the specified JSON format." } ] ```;

                loop invariant i_7: s in the specified JSON format." } ] ```;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
