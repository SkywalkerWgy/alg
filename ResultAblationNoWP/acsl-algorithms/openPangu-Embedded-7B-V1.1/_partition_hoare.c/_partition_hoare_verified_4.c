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
        loop invariant i_80: \forall integer k; 0 <= k < i <= j <= h;

        loop invariant i_81: \forall integer k; a[k] <= pivot || k == i;

        loop invariant i_82: \forall integer k; a[k] >= pivot || k == j;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_87: \forall integer k; 0 <= k < j <= h;

            loop invariant i_88: \forall integer k; a[k] <= pivot || k == i;

            loop invariant i_89: \forall integer k; a[k] >= pivot || k == j;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_83: \forall integer k; 0 <= k < j <= h;

            loop invariant i_84: \forall integer k; a[k] <= pivot || k == i;

            loop invariant i_85: \forall integer k; 0 <= k < i <= j <= h;

            loop invariant i_86: \forall integer k; a[k] >= pivot || k == j;


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