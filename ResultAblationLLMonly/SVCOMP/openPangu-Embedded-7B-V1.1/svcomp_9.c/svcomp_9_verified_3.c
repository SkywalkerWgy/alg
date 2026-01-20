/*@
    requires 0 < n;
*/
int svcomp_9(int n) {
	int k = 0;
	int i = 0;

    // Loop A
	/*@
        loop invariant i_16: i + k == j;

        loop invariant i_17: k >= 0 && j >= i;

        loop invariant i_18: i < n;

        loop invariant i_19: k < n;


        loop assigns i, k;
    */
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	
    // Loop B
    /*@
        loop invariant i_20: k >= 0 && j >= i;

        loop invariant i_21: i + k == j;

        loop invariant i_22: i < n && k < n;

        loop invariant i_23: j <= k;

        loop invariant i_24: k >= 0 && i >= 0;

        loop invariant i_25: j >= 0 && k >= 0;

        loop invariant i_26: j <= k && k >= 0 && j <= n;

        loop invariant i_27: k < n;

        loop invariant i_28: j <= n && k >= 0;

        loop invariant i_29: i >= 0 && k >= 0 && i <= j;

        loop invariant i_30: j >= 0 && k == j;

        loop invariant i_31: k >= 0 && j >= i && i < n;

        loop invariant i_32: j >= 0 && k >= 0 && j <= n;


        loop assigns j, k;
    */
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}