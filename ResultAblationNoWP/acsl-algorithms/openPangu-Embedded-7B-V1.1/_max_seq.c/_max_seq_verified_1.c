/*@ requires n >= 0;
    requires \valid(a + (0..n-1));

    assigns \nothing;

    behavior empty:
      assumes n == 0;
      ensures e_1: \result == 0;
    behavior not_empty:
      assumes 0 < n;
      ensures e_2: 0 <= \result < n;
      ensures e_3: \forall integer i; 0 <= i < n ==> a[i] <= a[\result];
    complete behaviors;
    disjoint behaviors;
*/
int _max_seq(int *a, int n) {
    if (n == 0) {
        return 0;
    }
    int max = 0;

    // Loop A
    /*@
        loop invariant i_0: n >= 1 || n == 0;

        loop invariant i_1: \exists integer max; 0 <= max < n;

        loop invariant i_2: \forall integer i; 0 <= i < n ==> a[i] <= a[max];


        loop assigns max, i;
    */
    for (int i = 1; i < n; i++) {
        if (a[max] < a[i]) {
            max = i;
        }
    }
    return max;
}