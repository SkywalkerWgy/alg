/*@
  predicate sorted(int *t, integer lo, integer hi) =
    \forall integer i, j; lo <= i <= j < hi ==> t[i] <= t[j];
*/

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

/*@ requires \valid(arr+(0..(n - 1)));
    requires n > 0;
    ensures e_1: sorted(arr, 0, n);
    assigns arr[0..(n - 1)];
*/
void _select_sort(int* arr, int n)
{
    // Loop A
    /*@
        loop invariant i_0: 0 <= i < n;

        loop invariant i_1: sorted(arr, 0, i);

        loop invariant i_2: \forall integer k; i <= k < n ==> arr[k] >= arr[i-1];

        loop invariant i_3: \forall integer p, q; 0 <= p < i ==> i <= q < n ==> arr[p] <= arr[q];

        loop invariant i_8: i == 0 ==> \forall integer k; 0 <= k < n ==> arr[k] >= arr[0-1];

        loop invariant i_9: i > 0 ==> \forall integer k; i <= k < n ==> arr[k] >= arr[i-1];

        loop invariant i_10: i == 0 || \forall integer p, q; 0 <= p < q < i ==> arr[p] <= arr[q];

        loop invariant i_11: i == 0 || \forall integer k; i <= k < n ==> arr[k] >= arr[i-1];

        loop invariant i_13: \forall integer p, q; 0 <= p < i <= q < n ==> arr[p] <= arr[q];

        loop invariant i_14: i == 0 || \forall integer k; 0 <= k < n ==> arr[k] >= arr[0-1];


        loop assigns i, arr[0..(n - 1)];
    */
    for (int i = 0; i < n - 1; i++)
    {
        int min = i;
        // Loop B
        /*@
            loop invariant i_4: i <= j <= n;

            loop invariant i_5: min >= i;

            loop invariant i_6: \forall integer k; i <= k < j ==> arr[min] <= arr[k];

            loop invariant i_7: \forall integer k; i <= k < j ==> arr[k] >= arr[i-1];

            loop invariant i_12: \forall integer k; 0 <= k < i ==> arr[k] <= arr[min];


            loop assigns j, min;
        */
        for (int j = i; j < n; j++){  
            if (arr[j] < arr[min]){
                min = j;    
            }
        } 
        swap(&arr[min], &arr[i]);   
    }
}