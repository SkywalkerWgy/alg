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
        loop invariant i_26: lo <= i <= j <= hi && a[i] <= pivot || a[j] >= pivot && a[lo..hi] is partitioned by pivot;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_27: i <= j && a[i] <= pivot && a[j] >= pivot && lo <= i <= j && a[lo..i] is partitioned by pivot && a[i] <= pivot;

            loop invariant i_30: i <= j && a[i] <= pivot || a[j] >= pivot && lo <= i <= j && a[lo..i] is partitioned by pivot && a[i] <= pivot;

            loop invariant i_31: j >= i && a[i] <= pivot || a[j] >= pivot && lo <= i <= j && a[lo..j] is partitioned by pivot;

            loop invariant i_32: lo <= i <= j <= hi && a[i] <= pivot || a[j] >= pivot && a[lo..i] is partitioned by pivot && a[i] <= pivot;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_28: j >= i && a[i] <= pivot || a[j] >= pivot && lo <= i <= j && a[lo..j] is partitioned by pivot && a[j] >= pivot;

            loop invariant i_29: i <= j && a[i] <= pivot || a[j] >= pivot && lo <= i <= j && a[lo..j] is partitioned by pivot && a[j] >= pivot;


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