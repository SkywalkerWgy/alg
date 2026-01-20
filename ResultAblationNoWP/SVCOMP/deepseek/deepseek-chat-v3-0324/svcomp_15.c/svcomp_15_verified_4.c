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
        loop invariant i_15: 1 <= k <= n;

        loop invariant i_16: l <= n;

        loop invariant i_17: l >= \at(l, Pre);

        loop invariant i_18: \forall integer j; \at(l, Pre) <= j < l ==> unknown1() was true at iteration j;


        loop assigns i, k, l;
    */
    for (k = 1; k < n; k++){
        // Loop B
        /*@
            loop invariant i_19: l <= i <= n;

            loop invariant i_20: \forall integer j; \at(l, Pre) <= j < l ==> unknown1() was true at iteration j;


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