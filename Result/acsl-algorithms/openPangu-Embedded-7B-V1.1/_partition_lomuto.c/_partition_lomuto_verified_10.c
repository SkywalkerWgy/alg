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
        loop invariant i_1: \forall integer k; lo <= k <= i ==> a[k] <= pivot;

        loop invariant i_2: \forall integer k; lo <= k <= i ==> a[k] <= a[hi];

        loop invariant i_3: i >= lo - 1;

        loop invariant i_4: j >= lo;

        loop invariant i_6: \forall integer k; lo <= k <= i ==> a[k] <= a[hi] && a[k] <= pivot;

        loop invariant i_7: \forall integer k; lo <= k <= i ==> a[k] <= pivot && a[k] <= a[hi];


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