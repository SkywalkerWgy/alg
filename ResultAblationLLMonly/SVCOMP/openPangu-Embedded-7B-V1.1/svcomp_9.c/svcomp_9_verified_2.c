/*@
    requires 0 < n;
*/
int svcomp_9(int n) {
	int k = 0;
	int i = 0;

    // Loop A
	/*@
        loop invariant i_10: i + k == j;

        loop invariant i_11: 0 <= i && i < n && 0 < j && k >= 0;

        loop invariant i_12: j >= 0 || k == 0;


        loop assigns i, k;
    */
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	
    // Loop B
    /*@
        loop invariant i_13: j + k == n;

        loop invariant i_14: 0 <= i && i < n && 0 <= k;

        loop invariant i_15: j >= 0 && k >= 0;


        loop assigns j, k;
    */
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}