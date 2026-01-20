/*@
    requires \valid(x) && \valid(y);
    assigns *x, *y;
    ensures *x == \old(*y) && *y == \old(*x);
*/
void swap(int *x, int *y) {
    int tmp = *x;
    *x = *y;
    *y = tmp;
}

/*@
    requires lo <= hi;
    requires \valid(a + (lo .. hi));
    assigns a[lo..hi];
    ensures lo <= \result && \result <= hi;
    ensures e_1: \forall integer i; lo <= i <= \result ==> a[i] <= a[\result];
    ensures e_2: \forall integer i; \result <= i <= hi ==> a[i] >= a[\result];
*/
int _partition_lomuto(int* a, int lo, int hi) {
    int pivot = a[hi];
    int i = lo - 1;
    int j;

    // Loop A
    /*@
        loop invariant i_7: : \forall integer k; lo <= k < hi ==> a[k] <= pivot && \texttt{?};

        loop invariant i_8: j == lo + \texttt{i};

        loop invariant i_9: \exists integer j; lo <= j < hi && a[j] <= pivot;

        loop invariant i_10: *a[j] == a[lo + \texttt{i}];

        loop invariant i_11: \forall integer k; \texttt{i} < k < \texttt{j} ==> a[k] > pivot;

        loop invariant i_12: \forall integer k; k < \texttt{?} ==> a[k] <= pivot;

        loop invariant i_13: \texttt{i} >= \texttt{j};

        loop invariant i_14: \texttt{i} < \texttt{j};

        loop invariant i_15: \exists integer j; \texttt{i} >= \texttt{j} && \texttt{i} < \texttt{j} ==> a[\texttt{i} + \texttt{j}] == pivot;

        loop invariant i_16: \forall integer k; \texttt{i} <= k <= \texttt{j} && a[\texttt{i} + \texttt{k}] == pivot;

        loop invariant i_17: \texttt{j} == \texttt{i} + 1;


        loop assigns a[lo..hi], i, j;
    */
    for (j = lo; j < hi; j++) {
        if (a[j] <= pivot) {
            i++;
            swap(&a[i], &a[j]);
        }
    }
    swap(&a[i + 1], &a[hi]);
    return i + 1;
}