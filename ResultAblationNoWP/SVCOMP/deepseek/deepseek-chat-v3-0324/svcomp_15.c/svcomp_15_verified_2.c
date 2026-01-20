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
        loop invariant i_5: 1 <= k <= n;

        loop invariant i_6: l >= \at(l, Pre) && l <= \at(l, Pre) + k - 1;

        loop invariant i_7: \forall integer m; 0 <= m < k ==> l <= \at(l, Pre) + m;


        loop assigns i, k, l;
    */
    for (k = 1; k < n; k++){
        // Loop B
        /*@
            loop invariant i_8: l <= i <= n;

            loop invariant i_9: \forall integer p; l <= p < i ==> 1 <= p;


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