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
        loop invariant i_29: \forall integer k; 0 <= k < i ==> max >= a[k];

        loop invariant i_30: \forall integer p; 0 <= p < j ==> a[p] <= pivot;

        loop invariant i_31: \forall integer k; 0 <= k < j && a[k] <= pivot ==> a[k] >= min;

        loop invariant i_32: i <= j;

        loop invariant i_33: lo <= i <= hi;

        loop invariant i_34: \exists integer k; 0 <= k < i && max == a[k];

        loop invariant i_35: \forall integer k; 0 <= k < i && max == a[k] && a[k] <= pivot ==> a[k] >= min;

        loop invariant i_36: 0 <= i <= j;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_45: \forall integer k; 0 <= k < i ==> max >= a[k];

            loop invariant i_46: \forall integer p; 0 <= p < j ==> a[p] <= pivot;

            loop invariant i_47: \forall integer k; 0 <= k < j && a[k] <= pivot ==> a[k] >= min;

            loop invariant i_48: i <= j;

            loop invariant i_49: lo <= i <= hi;

            loop invariant i_50: \exists integer k; 0 <= k < i && max == a[k];

            loop invariant i_51: \forall integer k; 0 <= k < i && max == a[k] && a[k] <= pivot ==> a[k] >= min;

            loop invariant i_52: 0 <= i <= j;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_37: \forall integer k; 0 <= k < i ==> max >= a[k];

            loop invariant i_38: \forall integer p; 0 <= p < j ==> a[p] <= pivot;

            loop invariant i_39: \forall integer k; 0 <= k < j && a[k] <= pivot ==> a[k] >= min;

            loop invariant i_40: i <= j;

            loop invariant i_41: lo <= i <= hi;

            loop invariant i_42: \exists integer k; 0 <= k < i && max == a[k];

            loop invariant i_43: \forall integer k; 0 <= k < i && max == a[k] && a[k] <= pivot ==> a[k] >= min;

            loop invariant i_44: 0 <= i <= j;


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