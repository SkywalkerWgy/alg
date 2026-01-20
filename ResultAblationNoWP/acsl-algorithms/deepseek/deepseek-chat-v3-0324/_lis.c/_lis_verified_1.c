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
        loop invariant i_0: \forall integer k; 0 <= k < i ==> dp[k] == 1 || (\exists integer m; 0 <= m < k && arr[m] < arr[k] && dp[k] == dp[m] + 1); loop invariant \forall integer k; 0 <= k < i ==> dp[k] >= 1;

        loop invariant i_1: \forall integer k; 0 <= k < i ==> dp[k] >= 1;

        loop invariant i_2: \forall integer p, q; 0 <= q < p < i && arr[q] < arr[p] ==> dp[p] >= dp[q] + 1;

        loop invariant i_3: \forall integer k; 0 <= k < n ==> dp[k] == \at(dp[k], Pre) || (0 <= k < i && dp[k] > 1);


        loop assigns dp[0..(n - 1)];
        loop assigns i;
    */
    for (int i = 0; i < n; i++) {
        //@ ghost int cur = -1; 
        // Loop B
        /*@
            loop invariant i_8: \forall integer k; 0 <= k < j && arr[k] < arr[i] ==> dp[i] >= dp[k] + 1;

            loop invariant i_9: dp[i] == 1 || (\exists integer m; 0 <= m < j && arr[m] < arr[i] && dp[i] == dp[m] + 1); loop invariant dp[i] >= 1;

            loop invariant i_10: dp[i] >= 1;


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
        loop invariant i_4: \forall integer k; 0 <= k < i ==> ans >= dp[k];

        loop invariant i_5: \exists integer k; 0 <= k < i && ans == dp[k];

        loop invariant i_6: \forall integer k; 0 <= k < n ==> dp[k] == \at(dp[k], Pre) || (0 <= k < i && dp[k] > 1);

        loop invariant i_7: ans == dp[res];


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