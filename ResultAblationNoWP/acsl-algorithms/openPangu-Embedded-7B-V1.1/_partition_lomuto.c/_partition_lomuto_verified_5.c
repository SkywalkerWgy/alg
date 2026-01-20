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
        loop invariant i_23: lo <= i < hi && \forall integer k; lo <= k <= i ==> a[k] <= pivot;

        loop invariant i_24: \exists integer j; 0 <= j <= hi && (j == i || a[j] > pivot);

        loop invariant i_25: lo <= \result <= hi && \forall integer i; lo <= i <= \result ==> a[i] <= a[\result];

        loop invariant i_26: \forall integer i; \result <= i <= hi ==> a[i] >= a[\result];


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