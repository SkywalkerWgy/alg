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
        loop invariant i_0: 0 <= i <= j;

        loop invariant i_1: 0 <= j <= hi;

        loop invariant i_2: i <= j;

        loop invariant i_3: a[i] <= pivot;

        loop invariant i_4: a[j] >= pivot;

        loop invariant i_5: \exists integer k; 0 <= k < i && a[k] == pivot;

        loop invariant i_6: \forall integer k; 0 <= k < j && a[k] <= pivot && a[k] == pivot;

        loop invariant i_7: \forall integer k; 0 <= k < i ==> a[k] <= pivot;

        loop invariant i_8: \forall integer k; 0 <= k < j ==> a[k] >= pivot;

        loop invariant i_9: 0 <= i < lo && 0 <= j <= hi;

        loop invariant i_10: \forall integer k; 0 <= k < i <= j && a[k] <= pivot;

        loop invariant i_11: \forall integer k; 0 <= k < j >= i && a[k] >= pivot;

        loop invariant i_12: 0 <= i < lo;

        loop invariant i_13: 0 <= j > hi;

        loop invariant i_14: a[i] == pivot;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_17: 0 <= i <= j;

            loop invariant i_18: 0 <= j <= hi;

            loop invariant i_19: i <= j;

            loop invariant i_20: a[i] <= pivot;

            loop invariant i_21: a[j] >= pivot;

            loop invariant i_22: \exists integer k; 0 <= k < i && a[k] == pivot;

            loop invariant i_23: \forall integer k; 0 <= k < j && a[k] <= pivot && a[k] == pivot;

            loop invariant i_24: \forall integer k; 0 <= k < i ==> a[k] <= pivot;

            loop invariant i_25: \forall integer k; 0 <= k < j ==> a[k] >= pivot;

            loop invariant i_26: 0 <= i < lo;

            loop invariant i_27: 0 <= j > hi;

            loop invariant i_28: a[i] == pivot;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_15: 0 <= j <= hi;

            loop invariant i_16: 0 <= i < lo;


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