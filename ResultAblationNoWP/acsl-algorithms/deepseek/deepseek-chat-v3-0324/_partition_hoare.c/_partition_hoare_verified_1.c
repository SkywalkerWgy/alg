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
        loop invariant i_0: lo <= i && i <= hi && lo <= j && j <= hi;

        loop invariant i_1: \forall integer k; lo <= k < i ==> a[k] <= pivot;

        loop invariant i_2: \forall integer k; j < k <= hi ==> a[k] >= pivot;

        loop invariant i_3: \forall integer k; lo <= k <= hi ==> \exists integer l; lo <= l <= hi && a[k] == \old(a[l]);

        loop invariant i_4: i <= j + 1;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_8: lo <= j && j <= hi;

            loop invariant i_9: \forall integer k; j < k <= hi ==> a[k] >= pivot;

            loop invariant i_10: \forall integer k; lo <= k <= hi ==> \exists integer l; lo <= l <= hi && a[k] == \old(a[l]);


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_5: lo <= i && i <= hi;

            loop invariant i_6: \forall integer k; lo <= k < i ==> a[k] < pivot;

            loop invariant i_7: \forall integer k; lo <= k <= hi ==> \exists integer l; lo <= l <= hi && a[k] == \old(a[l]);


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