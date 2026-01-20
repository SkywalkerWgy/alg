/*@ requires n >= 0;
    requires \valid(a + (0..n-1));

    assigns \nothing;

    behavior empty:
      assumes n == 0;
      ensures e_1: \result == 0;
    behavior not_empty:
      assumes e_2: 0 < n;
      ensures e_3: 0 <= \result < n;
      ensures e_4: \forall integer i; 0 <= i < n ==> a[i] >= a[\result];
    complete behaviors;
    disjoint behaviors;
*/
int _min_seq(int *a, int n) {
    if (n == 0) {
        return 0;
    }
    int min = 0;

    // Loop A
    /*@
        loop invariant i_0: 0 <= n;

        loop invariant i_3: \forall integer i; 0 <= i < n ==> min < n;

        loop invariant i_5: \forall integer i; 0 <= i < n ==> \exists integer k; 0 <= k < n;

        loop invariant i_6: \forall integer i; 0 <= i < n ==> min <= n - 1;

        loop invariant i_7: n >= 1;

        loop invariant i_8: \forall integer i; 0 <= i < n ==> \exists integer k; 0 <= k < n && a[k] >= a[min];

        loop invariant i_9: n >= 0;

        loop invariant i_10: \forall integer i; 0 <= i < n ==> min >= 0;

        loop invariant i_11: \forall integer i; 0 <= i < n ==> min >= 0 && min < n;

        loop invariant i_12: \forall integer i; 0 <= i < n ==> a[i] >= a[min];


        loop assigns min, i;
    */
    for (int i = 1; i < n; i++) {
        if (a[min] > a[i]) {
            min = i;
        }
    }
    return min;
}