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
        loop invariant i_10: 1 <= k <= n;

        loop invariant i_11: l <= n;

        loop invariant i_12: \forall integer j; l <= j < i ==> 1 <= j;


        loop assigns i, k, l;
    */
    for (k = 1; k < n; k++){
        // Loop B
        /*@
            loop invariant i_13: l <= i <= n;

            loop invariant i_14: \forall integer j; l <= j < i ==> 1 <= j;


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