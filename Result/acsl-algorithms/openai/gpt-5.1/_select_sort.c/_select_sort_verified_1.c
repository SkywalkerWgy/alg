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
        loop invariant i_0: \valid(arr + (0..(n - 1)));

        loop invariant i_1: n > 0;

        loop invariant i_2: 0 <= i <= n - 1;

        loop invariant i_3: sorted(arr, 0, i);

        loop invariant i_4: \forall integer k1, k2; 0 <= k1 < i <= k2 < n ==> arr[k1] <= arr[k2];


        loop assigns i, arr[0..(n - 1)];
    */
    for (int i = 0; i < n - 1; i++)
    {
        int min = i;
        // Loop B
        /*@
            loop invariant i_5: \valid(arr + (0..(n - 1)));

            loop invariant i_6: n > 0;

            loop invariant i_7: 0 <= i <= n - 1;

            loop invariant i_8: sorted(arr, 0, i);

            loop invariant i_9: \forall integer k1, k2; 0 <= k1 < i <= k2 < n ==> arr[k1] <= arr[k2];

            loop invariant i_10: i <= j <= n;

            loop invariant i_11: (j == i && min == i) || (i <= min < j);

            loop invariant i_12: \forall integer k; i <= k < j ==> arr[min] <= arr[k];


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