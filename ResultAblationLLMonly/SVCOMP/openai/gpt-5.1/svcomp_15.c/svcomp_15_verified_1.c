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
        loop invariant i_0: 1 <= k <= n;

        loop invariant i_1: l >= 1;


        loop assigns i, k, l;
    */
    for (k = 1; k < n; k++){
        // Loop B
        /*@
            loop invariant i_2: 1 <= i;

            loop invariant i_3: l <= i;


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