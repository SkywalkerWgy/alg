/*@
    predicate connect(int** graph, integer i, integer j, integer n) =
        0 <= i < n && 0 <= j < n && ((i == j) || (graph[i][j] == 1) || (graph[j][i] == 1) || (\exists integer k; 0 <= k < n && connect(graph, i, k, n) && connect(graph, k, j, n)));
*/

/*@
    requires 0 <= start < n;
    requires \valid(graph + (0..(n)));
    requires \valid(graph[0..(n)] + (0..(n)));
    requires \valid(dist + (0..(n)));
    requires \valid(visited + (0..(n)));
    requires \valid(stack + (0..(n)));
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n && i != j ==> \separated(&graph[i] + (0..(n)), &graph[j] + (0..(n)), &dist[0..(n)], &visited[0..(n)], &stack[0..(n)]);
    requires \separated(&dist[0..(n)], &visited[0..(n)], &stack[0..(n)]);
    requires \forall integer j; 0 <= j <= n && j != start ==> visited[j] == 0 && dist[j] == -1;
    requires visited[start] == 1 && dist[start] == 0;
    requires stack[0] == start;
    requires \forall integer i, j; 0 <= i <= n ==> graph[i][i] == 1;
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n ==> graph[i][j] == graph[j][i];
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n ==> (graph[i][j] == 0 || graph[i][j] == 1);
    ensures e_1: \forall integer i; (0 <= i < n && visited[i] == 1) ==> connect(graph, i, start, n);
    assigns dist[0..(n)], visited[0..(n)], stack[0..(n)];
*/
void _dfs(int** graph, int* dist, int* visited, int* stack, int start, int n) {
    int top = 0;
    int node = start;
    // Loop A
    /*@
        loop invariant i_0: 0 <= top < n;

        loop invariant i_1: \forall integer k; 0 <= k < top ==> 0 <= stack[k] < n;

        loop invariant i_2: \forall integer k; 0 <= k < n && visited[k] == 1 ==> connect(graph, start, k, n);

        loop invariant i_3: \forall integer k; 0 <= k < n && visited[k] == 1 ==> dist[k] == \at(dist[k], Pre);

        loop invariant i_4: node == stack[top] || (top == -1 && node == \at(node, LoopEntry));

        loop invariant i_5: \forall integer k; 0 <= k <= top ==> visited[stack[k]] == 1;

        loop invariant i_6: \forall integer k; 0 <= k <= top ==> dist[stack[k]] == \at(dist[stack[k]], Pre);

        loop invariant i_7: \forall integer k; 0 <= k < n && visited[k] == 1 ==> 0 <= dist[k] < n;

        loop invariant i_8: \forall integer k; 0 <= k <= top ==> 0 <= stack[k] < n;


        loop assigns top;
        loop assigns node;
        loop assigns stack[0..(n)];
        loop assigns dist[0..(n)];
        loop assigns visited[0..(n)];
    */
    while (0 <= top && top < n) {
        // Loop B
        /*@
            loop invariant i_9: 0 <= i <= n;

            loop invariant i_10: \forall integer k; 0 <= k < i ==> (graph[node][k] == 1 && visited[k] == 0 && top < n) ==> (visited[k] == 1 && dist[k] == dist[node] + 1 && stack[top] == k && top == \at(top, LoopEntry) + 1);

            loop invariant i_11: \forall integer k; 0 <= k < i ==> (graph[node][k] == 0 || visited[k] == 1 || top >= n) ==> (visited[k] == \at(visited[k], LoopEntry) && dist[k] == \at(dist[k], LoopEntry));

            loop invariant i_12: \forall integer k; 0 <= k < n && visited[k] == 1 ==> connect(graph, start, k, n);

            loop invariant i_13: \forall integer k; 0 <= k < n && visited[k] == 1 ==> dist[k] >= 0 && dist[k] < n;

            loop invariant i_14: \forall integer k; 0 <= k <= top ==> 0 <= stack[k] < n && visited[stack[k]] == 1;

            loop invariant i_15: \forall integer k; 0 <= k <= top ==> dist[stack[k]] == \at(dist[stack[k]], LoopEntry);

            loop invariant i_16: 0 <= top < n;

            loop invariant i_17: node == stack[top] || (top == -1 && node == \at(node, LoopEntry));

            loop invariant i_18: \forall integer k; 0 <= k <= \at(top, LoopEntry) ==> dist[stack[k]] == \at(dist[stack[k]], LoopEntry);

            loop invariant i_19: \forall integer k; 0 <= k < i && k != i ==> (graph[node][k] == 0 || visited[k] == 1 || top >= n) ==> (visited[k] == \at(visited[k], LoopEntry) && dist[k] == \at(dist[k], LoopEntry));

            loop invariant i_20: (graph[node][i] == 0 || visited[i] == 1 || top >= n) ==> (visited[i] == \at(visited[i], LoopEntry) && dist[i] == \at(dist[i], LoopEntry));

            loop invariant i_21: \forall integer k; 0 <= k < i && visited[k] == 1 ==> graph[node][k] == \at(graph[node][k], LoopEntry);

            loop invariant i_22: \forall integer k; 0 <= k <= top ==> \at(stack[top], LoopEntry) == \at(stack[top], Here);

            loop invariant i_23: \forall integer k; 0 <= k < i && visited[k] == 1 ==> dist[k] <= \at(dist[k], LoopEntry);

            loop invariant i_24: \forall integer k; \at(top, LoopEntry) < k <= top ==> dist[stack[k]] == dist[stack[top]] - (top - k);

            loop invariant i_25: top >= \at(top, LoopEntry) ==> \forall integer k; 0 <= k <= \at(top, LoopEntry) ==> stack[k] == \at(stack[k], LoopEntry);

            loop invariant i_26: \forall integer k; 0 <= k <= top ==> dist[stack[k]] == dist[node] - (top - k);


            loop assigns top;
            loop assigns stack[0..(n)];
            loop assigns dist[0..(n)];
            loop assigns visited[0..(n)];
            loop assigns i;
        */
        for (int i = 0; i < n; i++) {
            if (graph[node][i] == 1 && visited[i] == 0 && top < n) { 
                top++;
                stack[top] = i;
                visited[i] = 1;
                dist[i] = dist[node] + 1;
            }
        }
        top -= 1;
        if(0 <= top){
            node = stack[top];
        }
        else{
            break;
        }
    }
}