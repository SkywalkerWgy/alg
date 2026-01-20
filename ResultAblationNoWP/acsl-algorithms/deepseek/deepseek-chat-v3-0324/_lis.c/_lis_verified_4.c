/*@
    requires n > 1;
    requires \valid(arr + (0..(n - 1)));
    requires \valid(dp + (0..(n - 1)));
    requires \separated(&arr[0..(n - 1)], &dp[0..(n - 1)]);
    requires \forall integer k; 0 <= k < n ==> dp[k] == 1;
    ensures e_1: \forall integer p, q; (0 <= q < p < n && arr[q] < arr[p]) ==> dp[p] >= dp[q] + 1;
    ensures e_2: \forall integer q; (0 <= q < n) ==> \result >= dp[q];
    ensures e_3: \exists integer q; (0 <= q < n) && \result == dp[q];
    assigns dp[0..(n - 1)];
*/
int _lis(int arr[], int n, int dp[]) {
    // Loop A
    /*@
        loop invariant i_34: \forall integer k; 0 <= k < i ==> dp[k] == \at(dp[k], Pre);

        loop invariant i_35: \forall integer p, q; (0 <= q < p < i && arr[q] < arr[p]) ==> dp[p] >= dp[q] + 1;

        loop invariant i_36: \forall integer q; 0 <= q < i ==> dp[q] >= 1;


        loop assigns dp[0..(n - 1)];
        loop assigns i;
    */
    for (int i = 0; i < n; i++) {
        //@ ghost int cur = -1; 
        // Loop B
        /*@
            loop invariant i_41: \forall integer k; 0 <= k < j ==> dp[i] >= dp[k] + (arr[k] < arr[i] ? 1 : 0);

            loop invariant i_42: \forall integer k; 0 <= k < j && arr[k] < arr[i] ==> dp[i] >= dp[k] + 1;

            loop invariant i_43: dp[i] >= 1;


            loop assigns dp[i];
            loop assigns j;
            loop assigns cur;
        */
        for (int j = 0; j < i; j++) {
            if (arr[j] < arr[i]){
                if (dp[i] < dp[j] + 1){
                    dp[i] = dp[j] + 1;
                    //@ ghost cur = j;
                }
            }
        }
    }

    //@ ghost int res = 0;
    int ans = dp[0];

    // Loop C
    /*@
        loop invariant i_37: \forall integer k; 0 <= k < i ==> ans >= dp[k];

        loop invariant i_38: \exists integer k; 0 <= k < i && ans == dp[k];

        loop invariant i_39: \forall integer k; 0 <= k < n ==> dp[k] >= 1;

        loop invariant i_40: \forall integer p, q; (0 <= q < p < n && arr[q] < arr[p]) ==> dp[p] >= dp[q] + 1;


        loop assigns i;
        loop assigns res;
        loop assigns ans;
    */
    for (int i = 0; i < n; i++) {
        if (dp[i] > ans) {
            ans = dp[i];
            //@ ghost res = i;
        }
    }

    return ans;
}