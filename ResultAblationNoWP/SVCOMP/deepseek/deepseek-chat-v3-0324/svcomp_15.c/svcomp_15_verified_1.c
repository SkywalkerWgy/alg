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

        loop invariant i_1: l >= \at(l, Pre) && l <= \at(l, Pre) + (k - 1);

        loop invariant i_2: \forall integer j; 1 <= j < k ==> l <= \at(l, Pre) + j;


        loop assigns i, k, l;
    */
    for (k = 1; k < n; k++){
        // Loop B
        /*@
            loop invariant i_3: l <= i <= n;

            loop invariant i_4: \forall integer j; l <= j < i ==> j < n;


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