/*@
  predicate sorted{Here}(int* a, integer start_index, integer end_index) =
    \forall integer k1, k2;
    start_index <= k1 <= k2 < end_index ==> a[k1] <= a[k2];
*/

/*@
  predicate swapped{L1,L2}(int* a, integer i, integer j) =
  \at(a[i],L1) == \at(a[j],L2) &&
  \at(a[j],L1) == \at(a[i],L2) &&
  \forall integer k; k != i && k != j
     ==> \at(a[k],L1) == \at(a[k],L2);
  */

/*@
  requires \valid(t+i) && \valid(t+j);
  assigns t[i],t[j];
  ensures \forall integer k; 0 <= k < n && k != i && k != j ==> t[k] == \old(t[k]);
  ensures swapped{Old,Here}(t,i,j);
  */
void sort_swap3(int t[], int i, int j, int n) {
    int tmp = t[i];
    t[i] = t[j];
    t[j] = tmp;
}

/*@
  requires 1 < length;
  requires \valid(a+(0..length-1));
  assigns a[0..length-1];
  ensures e_1: sorted(a, 0, length);
*/
void _bubble_sort(int *a, int length) {
    int up = 1;
    int down;

    // Loop A
    /*@
        loop invariant i_5: 0 <= up && up < length;

        loop invariant i_6: 0 <= down && down < up;

        loop invariant i_7: \forall integer k; 0 <= k < length ==> \at(a[k],Old) == Old;

        loop invariant i_8: \forall integer k; 0 <= k < down ==> \at(a[k],Old) == Old;

        loop invariant i_9: \forall integer k; down - 1 <= k < up && k != down - 1 ==> \at(a[k],Old) == Old && \at(a[down],Old) == Old;

        loop invariant i_10: 0 < down && down >= 0;

        loop invariant i_11: 0 <= down - 1 && \at(a[down - 1],Old) == Old;

        loop invariant i_12: \forall integer k; 0 <= k < down && k != down - 1 && \at(a[k],Old) == Old;

        loop invariant i_13: \forall integer k; 0 < down && \at(a[down - 1],Old) == Old && \at(a[down],Old) == Old;


        loop assigns down, up, a[0..length - 1];
    */
    for (; up < length; up++) {
        down = up;
      // Loop B
        /*@
          loop invariant i_14: 0 <= up && up < length;

          loop invariant i_15: 0 <= down && down < up;

          loop invariant i_16: \forall integer k; 0 <= k < length ==> \at(a[k],Old) == Old;

          loop invariant i_17: \forall integer k; 0 <= k < down ==> \at(a[k],Old) == Old;

          loop invariant i_18: down - 1 <= down && down >= 0 && \at(a[down - 1],Old) == Old && \at(a[down],Old) == Old;

          loop invariant i_19: 0 < down;

          loop invariant i_20: \forall integer k; down - 1 <= k < down && k != down - 1 && \at(a[k],Old) == Old;

          loop invariant i_21: \forall integer k; 0 < down && \at(a[down - 1],Old) == Old && \at(a[down],Old) == Old;


          loop assigns down, a[0..length - 1];          
        */
        while (0 < down && a[down] < a[down - 1]) {
            sort_swap3(a, down, down - 1, length);
            down = down - 1;
        }
    }
}