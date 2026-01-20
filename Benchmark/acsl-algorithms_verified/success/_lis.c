/*@
    requires n > 1;
    requires \valid(arr + (0..(n - 1)));
    requires \valid(dp + (0..(n - 1)));
    requires \separated(&arr[0..(n - 1)], &dp[0..(n - 1)]);
    requires \forall integer k; 0 <= k < n ==> dp[k] == 1;
    ensures \forall integer p, q; (0 <= q < p < n && arr[q] < arr[p]) ==> dp[p] >= dp[q] + 1;
    ensures \forall integer q; (0 <= q < n) ==> \result >= dp[q];
    ensures \exists integer q; (0 <= q < n) && \result == dp[q];
    assigns dp[0..(n - 1)];
*/
int _lis(int arr[], int n, int dp[]) {
    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer p, q; (0 <= q < p < i && arr[q] < arr[p]) ==> dp[p] >= dp[q] + 1;
        loop assigns dp[0..(n - 1)];
        loop assigns i;
    */
    for (int i = 0; i < n; i++) {
        /*@ ghost int cur = -1; */
        /*@
            loop invariant 0 <= j <= i;
            loop invariant \forall integer p, q; (0 <= q < p < i && arr[q] < arr[p]) ==> dp[p] >= dp[q] + 1;
            loop invariant \forall integer q; (0 <= q < j && arr[q] < arr[i]) ==> dp[i] >= dp[q] + 1;
            loop invariant cur == -1 || dp[i] == dp[cur] + 1;
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

    /*@ ghost int res = 0; */
    int ans = dp[0];
    /*@
        loop invariant 0 <= i <= n;
        loop invariant 0 <= res < n;
        loop invariant \forall integer q; (0 <= q < i) ==> ans >= dp[q];
        loop invariant ans == dp[res];
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