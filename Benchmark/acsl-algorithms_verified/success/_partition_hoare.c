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
    ensures lo <= \result && \result <= hi;
    ensures \forall integer i; lo <= i <= \result ==> a[i] <= a[\result];
    ensures \forall integer i; \result <= i <= hi ==> a[i] >= a[\result];
    assigns a[lo..hi];
*/
int _partition_hoare(int a[], int lo, int hi) {
    int pivot = a[lo];
    int i = lo;
    int j = hi;

    /*@
        loop invariant i1: lo <= i;
        loop invariant i2: i <= j;
        loop invariant i3: j <= hi;
        loop invariant i4: \forall integer k; lo <= k && k < i ==> a[k] < pivot;
        loop invariant i5: \forall integer k; j < k && k <= hi ==> a[k] > pivot;
        loop invariant i10: a[i] == pivot || a[j] == pivot;
        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        /*@
            loop invariant i6: j <= hi;
            loop invariant i7: \forall integer k; j < k && k <= hi ==> a[k] > pivot;
            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        /*@
            loop invariant i8: lo <= i;
            loop invariant i9: \forall integer k; lo <= k && k < i ==> a[k] < pivot;
            loop assigns i;
        */
        while (a[i] < pivot){
            i = i + 1;
        };

        if (i < j) {
            swap(&a[i], &a[j]);
        }
        else{
            return j;
        }
    }
}