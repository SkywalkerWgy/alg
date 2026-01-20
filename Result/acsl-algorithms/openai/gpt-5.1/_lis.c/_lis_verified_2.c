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
        loop invariant i_0: 0 <= i <= n;
        loop invariant i_1: n > 1;
        loop invariant i_2: \valid(arr + (0..(n - 1)));
        loop invariant i_3: \valid(dp + (0..(n - 1)));
        loop invariant i_4: \separated(&arr[0..(n - 1)], &dp[0..(n - 1)]);
        loop invariant i_5: \forall integer k; 0 <= k < i ==> dp[k] >= 1;
        loop invariant i_6: \forall integer k; i <= k < n ==> dp[k] == 1;
        loop invariant i_7: \forall integer p, q; 0 <= q < p < i && arr[q] < arr[p] ==> dp[p] >= dp[q] + 1;

        loop assigns dp[0..(n - 1)];
        loop assigns i;
    */
    for (int i = 0; i < n; i++) {
        //@ ghost int cur = -1; 
        // Loop B
        /*@
            loop invariant i_8: 0 <= i < n;
            loop invariant i_9: 0 <= j <= i;
            loop invariant i_10: n > 1;
            loop invariant i_11: \valid(arr + (0..(n - 1)));
            loop invariant i_12: \valid(dp + (0..(n - 1)));
            loop invariant i_13: \separated(&arr[0..(n - 1)], &dp[0..(n - 1)]);
            loop invariant i_14: \forall integer k; 0 <= k < i ==> dp[k] >= 1;
            loop invariant i_15: \forall integer k; i < k < n ==> dp[k] == 1;
            loop invariant i_16: dp[i] >= 1;
            loop invariant i_17: \forall integer q; 0 <= q < j && arr[q] < arr[i] ==> dp[i] >= dp[q] + 1;
            loop invariant i_18: cur == -1 || (0 <= cur < j && arr[cur] < arr[i] && dp[i] == dp[cur] + 1);

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
        loop invariant i_19: 0 <= i <= n;
        loop invariant i_20: n > 1;
        loop invariant i_21: \valid(arr + (0..(n - 1)));
        loop invariant i_22: \valid(dp + (0..(n - 1)));
        loop invariant i_23: \separated(&arr[0..(n - 1)], &dp[0..(n - 1)]);
        loop invariant i_24: \forall integer k; 0 <= k < n ==> dp[k] >= 1;
        loop invariant i_25: \forall integer p, q; 0 <= q < p < n && arr[q] < arr[p] ==> dp[p] >= dp[q] + 1;
        loop invariant i_26: 0 <= res < n;
        loop invariant i_27: \forall integer k; 0 <= k < i ==> ans >= dp[k];
        loop invariant i_28: 0 < i ==> (0 <= res < i && ans == dp[res]);
        loop invariant i_29: i == 0 ==> res == 0;
        loop invariant i_30: 0 < i ==> 0 <= res < i;
        loop invariant i_31: ans == dp[res];

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