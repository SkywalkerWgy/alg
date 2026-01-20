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
        loop invariant i_0: 1 <= l;

        loop invariant i_8: 1 <= l && l < INT_MAX;


        loop assigns i, k, l;
    */
    for (k = 1; k < n; k++){
        // Loop B
        /*@
            loop invariant i_3: 1 <= l && k < n && l < INT_MAX;

            loop invariant i_4: 1 <= l;

            loop invariant i_5: k < n;

            loop invariant i_6: l < INT_MAX;

            loop invariant i_7: i >= 1;

            loop invariant i_9: 1 <= l && l < INT_MAX;


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