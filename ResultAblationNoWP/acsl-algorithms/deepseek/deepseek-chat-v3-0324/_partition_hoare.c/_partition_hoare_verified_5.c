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
        loop invariant i_44: lo <= i <= hi && lo <= j <= hi;

        loop invariant i_45: \forall integer k; lo <= k < i ==> a[k] <= pivot;

        loop invariant i_46: \forall integer k; j < k <= hi ==> a[k] >= pivot;

        loop invariant i_47: \forall integer k; lo <= k <= hi ==> \exists integer l; lo <= l <= hi && a[k] == \old(a[l]);

        loop invariant i_48: i <= j + 1;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_52: lo <= j <= hi;

            loop invariant i_53: \forall integer k; j < k <= hi ==> a[k] >= pivot;

            loop invariant i_54: \forall integer k; lo <= k <= hi ==> \exists integer l; lo <= l <= hi && a[k] == \old(a[l]);


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_49: lo <= i <= hi;

            loop invariant i_50: \forall integer k; lo <= k < i ==> a[k] <= pivot;

            loop invariant i_51: \forall integer k; lo <= k <= hi ==> \exists integer l; lo <= l <= hi && a[k] == \old(a[l]);


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