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

        loop invariant i_1: \forall integer k; 0 <= k < i ==> max >= arr[k];

        loop invariant i_3: \exists min; \forall integer j; 0 <= j < i ==> arr[j] >= arr[min];

        loop invariant i_4: \forall integer k; 0 <= k < n && arr[k] == arr[min];

        loop invariant i_5: \forall integer m; max == \max(arr[0..(n - 1)]) && \forall integer j; 0 <= j < i ==> arr[j] <= max;

        loop invariant i_6: 0 <= arr[i] < n && \forall integer k; arr[k] < n;

        loop invariant i_7: \forall integer k; 0 <= k < i ==> max >= a[k];

        loop invariant i_8: \exists min; \forall integer j; 0 <= j < i ==> a[j] >= a[min];

        loop invariant i_9: \forall integer m; max == \max(a[0..(n - 1)]) && \forall integer j; 0 <= j < i ==> a[j] <= max;

        loop invariant i_10: 0 <= a[i] < n && \forall integer k; a[k] < n;


        loop assigns i, arr[0..(n - 1)];
    */
    for (int i = 0; i < n - 1; i++)
    {
        int min = i;
        // Loop B
        /*@
            loop invariant i_2: \forall integer k; 0 <= k < i ==> max >= arr[k];


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