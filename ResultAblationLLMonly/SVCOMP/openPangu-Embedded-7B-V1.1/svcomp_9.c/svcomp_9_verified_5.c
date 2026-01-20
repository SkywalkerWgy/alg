/*@
    requires 0 < n;
*/
int svcomp_9(int n) {
	int k = 0;
	int i = 0;

    // Loop A
	/*@
        loop invariant i_39: i + k == j;

        loop invariant i_40: 0 <= i && i < n;

        loop invariant i_41: k >= 0 && k < n;

        loop invariant i_42: j >= 0 && j <= n;


        loop assigns i, k;
    */
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	
    // Loop B
    /*@
        loop invariant i_43: 0 <= i && i < n;

        loop invariant i_44: 0 <= k && k < n;

        loop invariant i_45: j >= 0 && j <= n;

        loop invariant i_46: k > 0;


        loop assigns j, k;
    */
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}