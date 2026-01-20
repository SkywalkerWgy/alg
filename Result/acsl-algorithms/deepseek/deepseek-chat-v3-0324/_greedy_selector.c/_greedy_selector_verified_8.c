/*@
    predicate sorted(int *t, integer lo, integer hi) =
        \forall integer i, j; lo <= i <= j < hi ==> t[i] <= t[j];
*/

/*@ 
    requires \valid(s + (0..(n - 1)));
    requires \valid(f + (0..(n - 1)));
    requires \valid(selected + (0..(n - 1)));
    requires n > 0;
    requires sorted(f, 0, n);
    requires \separated(&s[0..(n - 1)], &f[0..(n - 1)], &selected[0..(n - 1)]);
    requires \forall integer k; 0 <= k < n ==> s[k] < f[k];
    requires \forall integer k; 0 <= k < n ==> selected[k] == 0;
    assigns selected[0..(n - 1)];
    ensures e_1: \forall integer p, q; (0 <= p < q < n && selected[p] == 1 && selected[q] == 1) ==> s[q] >= f[p];
*/
void _greedy_selector(int n, int* s, int* f, int* selected)
{
	int j = 0;
    selected[0] = 1;
    // Loop A
    /*@
        loop invariant i_0: 1 <= i <= n;
        loop invariant i_1: 0 <= j < n;
        loop invariant i_2: selected[j] == 1;
        loop invariant i_4: \forall integer p, q; 0 <= p < q < i && selected[p] == 1 && selected[q] == 1 ==> s[q] >= f[p];
        loop invariant i_5: \forall integer k; 0 <= k < i && selected[k] == 1 ==> (k == j || s[k] >= f[j]);
        loop invariant i_6: \forall integer k; 0 <= k < i && selected[k] == 1 && k != j ==> s[k] >= f[j];
        loop invariant i_7: selected[j] == 1 ==> \forall integer k; 0 <= k < i && selected[k] == 1 && k != j ==> s[k] >= f[j];
        loop invariant i_8: j == 0 ==> \forall integer k; 0 <= k < i && selected[k] == 1 ==> k == j;
        loop invariant i_9: j != 0 ==> \forall integer k; 0 <= k < i && selected[k] == 1 ==> s[k] >= f[j];
        loop invariant i_10: i == 1 ==> \forall integer k; 0 <= k < i && selected[k] == 1 ==> s[k] >= f[j];
        loop invariant i_11: i > 1 ==> \forall integer k; 0 <= k < i && selected[k] == 1 ==> s[k] >= f[j];

        loop assigns i, j, selected[0..(n - 1)];
    */
	for (int i = 1; i < n; i++){
		if (s[i] >= f[j]) { 
			selected[i] = 1;
			j = i;
		}
    }
}