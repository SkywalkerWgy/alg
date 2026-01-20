/*@
    requires 0 < n;
*/
int svcomp_9(int n) {
	int k = 0;
	int i = 0;

    // Loop A
	/*@
        loop invariant i_5: i <= n;

        loop invariant i_6: k >= 0;

        loop invariant i_7: i <= n && k >= 0;


        loop assigns i, k;
    */
	while (i < n) {
		i++;
		k++;
	}
	int j = n;
	
    // Loop B
    /*@
        loop invariant i_8: i <= n;

        loop invariant i_9: k >= 0;

        loop invariant i_10: i <= n && k >= 0;

        loop invariant i_11: k > 0;

        loop invariant i_12: j >= 0;


        loop assigns j, k;
    */
	while (j > 0) {
		//@ assert k > 0;
		j--;
		k--;
	}

	return 0;
}