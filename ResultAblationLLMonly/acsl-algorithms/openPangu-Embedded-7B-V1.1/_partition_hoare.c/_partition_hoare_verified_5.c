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
        loop invariant i_33: lo <= i <= j <= hi && a[lo] == pivot && a[i..j-1] == pivot;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_34: lo <= i <= hi;

            loop invariant i_37: lo <= i <= j <= hi && a[lo] == pivot && a[i..j-1] == pivot;

            loop invariant i_38: lo <= j <= hi;

            loop invariant i_39: lo <= i <= j <= hi && a[lo..j-1] == pivot && a[i] <= pivot && a[j] >= pivot;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_35: lo <= j <= hi;

            loop invariant i_36: lo <= i <= j <= hi && a[lo..j-1] == pivot && a[i] <= pivot && a[j] >= pivot;


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