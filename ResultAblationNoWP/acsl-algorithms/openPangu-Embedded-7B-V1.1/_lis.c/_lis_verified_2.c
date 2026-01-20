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
        loop invariant i_21: 0 <= i < n;

        loop invariant i_22: 0 <= j < i;

        loop invariant i_23: dp[i] == 0 || 0 <= j < i && arr[j] < arr[i] && dp[i] == dp[j] + 1;

        loop invariant i_24: dp[i] == dp[j] + 1 || dp[i] == 0;

        loop invariant i_25: ans <= dp[i];


        loop assigns dp[0..(n - 1)];
        loop assigns i;
    */
    for (int i = 0; i < n; i++) {
        //@ ghost int cur = -1; 
        // Loop B
        /*@
            loop invariant i_40: 0 <= i < n;

            loop invariant i_41: 0 <= j < i;

            loop invariant i_42: dp[i] == 0 || 0 <= j < i && arr[j] < arr[i] && dp[i] == dp[j] + 1;

            loop invariant i_43: dp[i] == dp[j] + 1 || dp[i] == 0;

            loop invariant i_44: ans <= dp[i];


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
        loop invariant i_26: 0 <= i < n;

        loop invariant i_27: 0 <= j < i;

        loop invariant i_28: dp[i] == 0 || 0 <= j < i && arr[j] < arr[i] && dp[i] == dp[j] + 1;

        loop invariant i_29: dp[i] == dp[j] + 1 || dp[i] == 0;

        loop invariant i_30: ans <= dp[i];

        loop invariant i_31: \forall integer k; 0 <= k < n && dp[k] == 0 || 0 <= j < k && arr[j] < arr[k] && dp[k] == dp[j] + 1;

        loop invariant i_32: \exists integer j; 0 <= j < i && arr[j] < arr[i] && dp[i] == dp[j] + 1;

        loop invariant i_33: ans == \max\{ dp[j] : 0 <= j < i && arr[j] < arr[i] && dp[j] > 0 \};

        loop invariant i_34: \forall integer p, q; 0 <= q < p < n && arr[q] < arr[p] ==> dp[p] >= dp[q] + 1;

        loop invariant i_35: \forall integer q; 0 <= q < n ==> dp[q] >= 0;

        loop invariant i_36: \exists integer q; 0 <= q < n && dp[q] == ans;

        loop invariant i_37: \forall integer k; 0 <= k < n && dp[k] == ans;

        loop invariant i_38: \forall integer k; 0 <= k < n && dp[k] >= ans;

        loop invariant i_39: \exists integer k; 0 <= k < n && dp[k] == ans;


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