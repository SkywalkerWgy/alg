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
        loop invariant i_33: lo <= i && i <= hi;

        loop invariant i_34: lo <= j && j <= hi;

        loop invariant i_35: \forall integer k; lo <= k < i ==> a[k] <= pivot;

        loop invariant i_36: \forall integer k; j < k <= hi ==> a[k] >= pivot;

        loop invariant i_37: i <= j + 1;

        loop invariant i_38: \valid(a + (lo .. hi));


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_42: lo <= j && j <= hi;

            loop invariant i_43: \forall integer k; j < k <= hi ==> a[k] >= pivot;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_39: lo <= i && i <= hi;

            loop invariant i_40: \forall integer k; lo <= k < i ==> a[k] <= pivot;

            loop invariant i_41: a[i] >= pivot;


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