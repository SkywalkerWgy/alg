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
        loop invariant i_90: 1 <= i <= j;

        loop invariant i_91: \forall integer k; 0 <= k < i || k == i || k > j;

        loop invariant i_92: a[i] < a[j] && a[i] != pivot;

        loop invariant i_93: \exists integer k; 0 <= k < i;

        loop invariant i_94: \forall integer k; 0 <= k < j || k == i || k > j;


        loop assigns a[lo..hi], i, j;
    */
    while (1) {
        // Loop B
        /*@
            loop invariant i_103: 1 <= i <= j;

            loop invariant i_104: \forall integer k; 0 <= k < i || k == i || k > j;

            loop invariant i_105: a[i] < a[j] && a[i] != pivot;

            loop invariant i_106: \exists integer k; 0 <= k < i;

            loop invariant i_107: \forall integer k; 0 <= k < j || k == i || k > j;

            loop invariant i_108: j >= lo;

            loop invariant i_109: i <= hi;

            loop invariant i_110: i <= j;

            loop invariant i_111: i == j || i + 1 == j;

            loop invariant i_112: \exists integer k; 0 <= k < j;

            loop invariant i_113: a[i] < pivot || a[j] == pivot;


            loop assigns j;
        */
        while (a[j] > pivot){
            j = j - 1;
        }

        // Loop C
        /*@
            loop invariant i_95: j >= lo;

            loop invariant i_96: i <= hi;

            loop invariant i_97: i <= j;

            loop invariant i_98: i == j || i + 1 == j;

            loop invariant i_99: \exists integer k; 0 <= k < i;

            loop invariant i_100: \exists integer k; 0 <= k < j;

            loop invariant i_101: a[i] < a[j] && a[i] != pivot;

            loop invariant i_102: a[i] < pivot || a[j] == pivot;


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