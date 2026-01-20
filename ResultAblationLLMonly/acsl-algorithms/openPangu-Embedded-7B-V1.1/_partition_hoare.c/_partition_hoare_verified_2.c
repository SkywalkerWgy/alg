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
        loop invariant i_7: 1 <= i <= j;

        loop invariant i_8: 1 <= k <= l;

        loop invariant i_9: *a[k] == pivot;

        loop invariant i_15: 1 <= i <= j && 1 <= k <= l;

        loop invariant i_16: 1 <= j <= hi;

        loop invariant i_17: 1 <= lo <= j && 1 <= i <= l;

        loop invariant i_18: 1 <= *a[i] <= *a[j];


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_14: 1 <= i <= j;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_10: 1 <= i <= j;

            loop invariant i_11: 1 <= k <= l;

            loop invariant i_12: *a[k] == pivot;

            loop invariant i_13: 1 <= i <= j && 1 <= k <= l;


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