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
    ensures e_1: \forall integer i; lo <= i <= \result ==> a[i] <= a[\result];
    ensures e_2: \forall integer i; \result <= i <= hi ==> a[i] >= a[\result];
    assigns a[lo..hi];
*/
int _partition_hoare(int a[], int lo, int hi) {
    int pivot = a[lo];
    int i = lo;
    int j = hi;

    // Loop A
    /*@
        loop invariant i_1: lo <= j && j <= hi;

        loop invariant i_2: \forall integer k; lo <= k <= i ==> a[k] <= pivot;

        loop invariant i_11: \forall integer k; j < k <= hi ==> a[k] >= pivot;

        loop invariant i_25: \forall integer k; lo <= k < j && k <= i ==> a[k] <= pivot;

        loop invariant i_27: \forall integer k; lo < k <= hi ==> a[k] >= pivot || a[k] <= pivot;

        loop invariant i_30: \forall integer k; lo < k < j && k <= i ==> a[k] <= pivot;

        loop invariant i_34: \forall integer k; j < k <= hi ==> a[k] > pivot;

        loop invariant i_37: \forall integer k; lo <= k < i ==> a[k] < pivot;

        loop invariant i_41: \forall integer k; lo < k < j && k <= i && k > lo ==> a[k] <= pivot;

        loop invariant i_42: j <= hi;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_5: lo <= j && j <= hi;

            loop invariant i_6: \forall integer k; j < k <= hi ==> a[k] > pivot;

            loop invariant i_12: \forall integer k; j < k <= hi ==> a[k] >= pivot;

            loop invariant i_13: \forall integer k; lo <= k <= i ==> a[k] <= pivot;

            loop invariant i_35: \forall integer k; lo <= k < i ==> a[k] < pivot;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_9: \forall integer k; lo <= k < i ==> a[k] < pivot;

            loop invariant i_14: \forall integer k; lo <= k < i ==> a[k] <= pivot;

            loop invariant i_16: a[j] <= pivot;

            loop invariant i_21: a[i] <= pivot || i == lo;

            loop invariant i_23: (i > lo) ==> (a[i] <= pivot);

            loop invariant i_36: \forall integer k; lo < k < i ==> a[k] < pivot;


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