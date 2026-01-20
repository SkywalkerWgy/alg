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
        loop invariant i_4: 0 <= i < n-1 && \valid(&arr[i]);

        loop invariant i_5: \exists integer min; 0 <= min <= i && arr[min] is the minimum in arr[0..i];

        loop invariant i_6: sorted(arr, 0, n-1);

        loop invariant i_7: 0 <= j <= n-1;

        loop invariant i_8: \exists integer min; min is the minimum in arr[0..i] and arr[min] is the minimum element in arr[0..i];

        loop invariant i_9: \forall integer k; arr[min] <= arr[k] for all k in [0..i];

        loop invariant i_10: \valid(&arr[min], &arr[i]);

        loop invariant i_11: arr[min] == the element at position min after swap;

        loop invariant i_12: arr[i] == the element at position i after swap;


        loop assigns i, arr[0..(n - 1)];
    */
    for (int i = 0; i < n - 1; i++)
    {
        int min = i;
        // Loop B
        /*@
            loop invariant i_13: 0 <= i < n-1 && \valid(&arr[i]);

            loop invariant i_14: \exists integer min; 0 <= min <= i && arr[min] is the minimum in arr[0..i];

            loop invariant i_15: sorted(arr, 0, n-1);

            loop invariant i_16: 0 <= j <= n-1;

            loop invariant i_17: \exists integer min; min is the minimum in arr[0..i] and arr[min] is the minimum element in arr[0..i];

            loop invariant i_18: \forall integer k; arr[min] <= arr[k] for all k in [0..i];

            loop invariant i_19: \valid(&arr[min], &arr[i]);

            loop invariant i_20: arr[min] == the element at position min after swap;

            loop invariant i_21: arr[i] == the element at position i after swap;


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