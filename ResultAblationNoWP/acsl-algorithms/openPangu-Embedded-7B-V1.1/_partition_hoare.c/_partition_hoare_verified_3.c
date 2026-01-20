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
        loop invariant i_53: && 1 <= lo && 1 <= hi;

        loop invariant i_54: \valid(a + (lo .. hi));

        loop invariant i_55: *x == \old(*y) && *y == \old(*x);

        loop invariant i_56: i <= j;

        loop invariant i_57: a[i] < pivot || i == lo;

        loop invariant i_58: a[j] > pivot || j == hi;

        loop invariant i_59: \exists integer k; 0 <= k < i && a[k] == pivot;

        loop invariant i_60: \exists integer k; 0 <= k < j && a[k] == pivot;

        loop invariant i_61: a[\result] == pivot;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_73: 1 <= lo && 1 <= hi;

            loop invariant i_74: \valid(a + (lo .. hi));

            loop invariant i_75: *x == \old(*y) && *y == \old(*x);

            loop invariant i_76: i <= j;

            loop invariant i_77: \exists integer k; 0 <= k < i && a[k] == pivot;

            loop invariant i_78: \exists integer k; 0 <= k < j && a[k] == pivot;

            loop invariant i_79: a[\result] == pivot;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_62: 1 <= lo && 1 <= hi;

            loop invariant i_63: \valid(a + (lo .. hi));

            loop invariant i_64: *x == \old(*y) && *y == \old(*x);

            loop invariant i_65: i <= j;

            loop invariant i_66: \forall integer i; 0 <= i <= \min(i, j) && a[i] < pivot;

            loop invariant i_67: \forall integer j; 0 <= j >= \max(i, j) && a[j] > pivot;

            loop invariant i_68: \exists integer k; 0 <= k < i && a[k] == pivot;

            loop invariant i_69: \exists integer k; 0 <= k < j && a[k] == pivot;

            loop invariant i_70: 1 <= i && 1 <= j;

            loop invariant i_71: \forall integer k; 0 <= k < i ==> a[k] < pivot;

            loop invariant i_72: \forall integer k; 0 <= k >= i && a[k] >= pivot;


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