/*@
  predicate Sorted(int *t, integer lo, integer hi) =
    \forall integer i, j; lo <= i <= j < hi ==> t[i] <= t[j];
*/

/*@
    requires \valid(d + (0..n - 1));
    requires \valid(f + (0..n - 1));
    requires \separated(&d[0..(n - 1)], &f[0..(n - 1)]);
    requires \forall integer k; 0 < k < n ==> f[k] == 0;
    requires d[0] == 0;
    requires f[0] == 1;
    requires n > 0;
    requires m > 0;
    requires Sorted(d, 0, n);
    assigns f[0..n - 1];
    ensures e_1: \exists integer k; 0 <= k < n && f[k] == 1 && \result <= d[k] + m;
*/
int _get_water(int d[], int f[], int n, int m) { 
	int maxDistance = m; 
    // Loop A
    /*@
        loop invariant i_0: 1 <= i <= n;
        loop invariant i_1: \forall integer k; 0 <= k < i ==> f[k] == (k == 0 ? 1 : (d[k] > maxDistance ? 1 : 0));
        loop invariant i_2: \forall integer k; i <= k < n ==> f[k] == 0;
        loop invariant i_4: Sorted(d, 0, n);
        loop invariant i_5: maxDistance == m + d[i-1] || maxDistance == m;
        loop invariant i_6: \forall integer k; 0 <= k < i-1 ==> d[k] <= maxDistance - m;
        loop invariant i_7: \exists integer k; 0 <= k < i && f[k] == 1;
        loop invariant i_8: maxDistance <= m + d[i-1];
        loop invariant i_9: \forall integer k; 0 <= k < i-1 ==> f[k] == (k == 0 ? 1 : (d[k] > maxDistance - m ? 1 : 0));
        loop invariant i_10: f[i-1] == (d[i-1] > maxDistance - m ? 1 : 0);
        loop invariant i_11: maxDistance == m + d[i-1] || (maxDistance == m && \forall integer k; 0 <= k < i-1 ==> d[k] <= m);
        loop invariant i_12: \forall integer k; 0 <= k < i-1 ==> d[k] <= maxDistance - m || maxDistance == m;
        loop invariant i_13: maxDistance >= m;
        loop invariant i_14: \forall integer k; 0 <= k < i-1 ==> f[k] == (d[k] > maxDistance - m ? 1 : 0) || maxDistance == m;
        loop invariant i_15: \forall integer k; 0 <= k < i-1 ==> d[k] <= m + d[i-2] || maxDistance == m;
        loop invariant i_16: i > 1 ==> d[i-2] <= maxDistance - m;
        loop invariant i_17: maxDistance == m || \exists integer k; 0 <= k < i-1 && maxDistance == m + d[k];
        loop invariant i_18: \exists integer k; 0 <= k < i && f[k] == 1 && maxDistance <= d[k] + m;
        loop invariant i_19: f[i-1] == (i == 1 ? 1 : (d[i-1] > maxDistance - m ? 1 : 0));
        loop invariant i_20: f[i-1] == (d[i-1] > maxDistance - m ? 1 : 0) || (i == 1 && f[i-1] == 1);
        loop invariant i_21: i == 1 ==> f[i-1] == 1;
        loop invariant i_22: i > 1 ==> f[i-1] == (d[i-1] > maxDistance - m ? 1 : 0);
        loop invariant i_23: (i == 1) ==> f[i-1] == 1;
        loop invariant i_24: (i > 1) ==> f[i-1] == (d[i-1] > maxDistance - m ? 1 : 0);
        loop invariant i_25: (i == 1) ? f[i-1] == 1 : f[i-1] == (d[i-1] > maxDistance - m ? 1 : 0);

        loop assigns i;
        loop assigns maxDistance;
        loop assigns f[0..n - 1];
    */
	for (int i = 1; i < n; i++) { 
		if (d[i] > maxDistance) { 
			f[i - 1] = 1;         
			maxDistance = m + d[i - 1];
		}
	}
    return maxDistance;
}
