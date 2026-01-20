/*@
    requires 0 < n;
*/
int svcomp_9(int n) {
	int k = 0;
	int i = 0;

    // Loop A
	/*@
        loop invariant i_0: i + k == j;

        loop invariant i_1: 0 <= i && i < n;

        loop invariant i_2: 0 < k;

        loop invariant i_3: j >= 0 && j <= n;


        loop assigns i, k;
    */
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	
    // Loop B
    /*@
        loop invariant i_4: k >= 0;

        loop invariant i_5: j >= 0 && j <= n;

        loop invariant i_6: j + k == n;

        loop invariant i_7: 0 <= i && i < n;

        loop invariant i_8: 0 < k;

        loop invariant i_9: i + k == j;


        loop assigns j, k;
    */
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}