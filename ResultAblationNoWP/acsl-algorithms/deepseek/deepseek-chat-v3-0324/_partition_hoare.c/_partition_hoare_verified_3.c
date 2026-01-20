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
        loop invariant i_22: lo <= i <= hi && lo <= j <= hi;

        loop invariant i_23: \forall integer k; lo <= k <= i ==> a[k] <= pivot;

        loop invariant i_24: \forall integer k; j <= k <= hi ==> a[k] >= pivot;

        loop invariant i_25: \forall integer k; lo <= k <= hi ==> \at(a[k], Pre) == a[k] || \at(a[k], Pre) == a[\at(j, Pre)] || \at(a[k], Pre) == a[\at(i, Pre)];

        loop invariant i_26: i <= j;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_30: lo <= j <= hi;

            loop invariant i_31: \forall integer k; j < k <= hi ==> a[k] > pivot;

            loop invariant i_32: \at(a[j], Pre) == a[j] || \at(a[j], Pre) == pivot;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_27: lo <= i <= hi;

            loop invariant i_28: \forall integer k; lo <= k < i ==> a[k] <= pivot;

            loop invariant i_29: \at(a[i], Pre) == a[i] || \at(a[i], Pre) == pivot;


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