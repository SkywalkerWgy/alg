/*@
    requires 0 < n;
*/
int svcomp_9(int n) {
	int k = 0;
	int i = 0;

    // Loop A
	/*@
        loop invariant i_33: i + k == j;

        loop invariant i_34: 0 <= i && 0 < n;

        loop invariant i_35: 0 <= k;

        loop invariant i_36: j >= 0;


        loop assigns i, k;
    */
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	
    // Loop B
    /*@
        loop invariant i_37: j >= 0 && j == n - i;

        loop invariant i_38: 0 <= k && k == j + k;


        loop assigns j, k;
    */
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}