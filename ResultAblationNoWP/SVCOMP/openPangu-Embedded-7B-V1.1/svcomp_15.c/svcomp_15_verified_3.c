# define INT_MAX 2147483647

int unknown1();

/*@
    requires l > 0;
    requires l < INT_MAX;
    requires n < INT_MAX;
*/
void svcomp_15(int n, int l) {
    int i, k;
    // Loop A
    /*@
        loop invariant i_8: 1 <= l;

        loop invariant i_9: l < INT_MAX;

        loop invariant i_10: k == k;

        loop invariant i_11: i == l;


        loop assigns i, k, l;
    */
    for (k = 1; k < n; k++){
        // Loop B
        /*@
            loop invariant i_12: 1 <= l;

            loop invariant i_13: l < INT_MAX;

            loop invariant i_14: k == k;

            loop invariant i_15: i == l;


            loop assigns i;
        */
        for (i = l; i < n; i++){  
            //@ assert 1 <= i;
        }
        if(unknown1()) {
            l = l + 1;
        }
    }
}