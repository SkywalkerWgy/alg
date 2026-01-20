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
    requires \valid(queue + (0..(n)));
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n && i != j ==> \separated(&graph[i] + (0..(n)), &graph[j] + (0..(n)), &dist[0..(n)], &visited[0..(n)], &queue[0..(n)]);
    requires \separated(&dist[0..(n)], &visited[0..(n)], &queue[0..(n)]);
    requires \forall integer j; 0 <= j <= n && j != start ==> visited[j] == 0 && dist[j] == -1;
    requires visited[start] == 1 && dist[start] == 0;
    requires queue[0] == start;
    requires \forall integer i, j; 0 <= i <= n ==> graph[i][i] == 1;
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n ==> graph[i][j] == graph[j][i];
    requires \forall integer i, j; 0 <= i <= n && 0 <= j <= n ==> (graph[i][j] == 0 || graph[i][j] == 1);
    ensures e_1: \forall integer i; (0 <= i < n && visited[i] == 1) ==> connect(graph, i, start, n);
    assigns dist[0..(n)], visited[0..(n)], queue[0..(n)];
*/
void _bfs(int** graph, int* dist, int* visited, int* queue, int start, int n) {
    int rear = 0;
    int front = 0;
    int node = start;
    // Loop A
    /*@
        loop invariant i_0: 0 <= front <= n;

        loop invariant i_1: 0 <= rear <= n;

        loop invariant i_2: front <= rear + 1;

        loop invariant i_3: 0 <= node < n;

        loop invariant i_4: 0 <= start < n;

        loop invariant i_5: visited[start] == 1;

        loop invariant i_6: dist[start] == 0;

        loop invariant i_7: queue[0] == start;

        loop invariant i_8: \forall integer j; 0 <= j < n && visited[j] == 0 ==> dist[j] == -1;

        loop invariant i_9: \forall integer j; 0 <= j < n && visited[j] == 1 ==> dist[j] >= 0;

        loop invariant i_10: \forall integer k; 0 <= k <= rear ==> 0 <= queue[k] < n && visited[queue[k]] == 1 && dist[queue[k]] >= 0;

        loop invariant i_11: \forall integer i; 0 <= i < n ==> (visited[i] == 1 ==> connect(graph, i, start, n));

        loop invariant i_12: connect(graph, node, start, n);

        loop invariant i_13: \forall integer i, j; 0 <= i < n && 0 <= j < n ==> graph[i][j] == graph[j][i];

        loop invariant i_14: \forall integer i; 0 <= i < n ==> graph[i][i] == 1;

        loop invariant i_15: \forall integer i, j; 0 <= i < n && 0 <= j < n ==> (graph[i][j] == 0 || graph[i][j] == 1);


        loop assigns front;
        loop assigns rear;
        loop assigns node;
        loop assigns queue[0..(n)];
        loop assigns dist[0..(n)];
        loop assigns visited[0..(n)];
    */
    while (front <= rear && front < n && rear < n) {
        // Loop B
        /*@
            loop invariant i_16: 0 <= i <= n;

            loop invariant i_17: 0 <= front <= n;

            loop invariant i_18: 0 <= rear <= n;

            loop invariant i_19: front <= rear + 1;

            loop invariant i_20: 0 <= node < n;

            loop invariant i_21: 0 <= start < n;

            loop invariant i_22: visited[start] == 1;

            loop invariant i_23: dist[start] == 0;

            loop invariant i_24: queue[0] == start;

            loop invariant i_25: \forall integer j; 0 <= j < n && visited[j] == 0 ==> dist[j] == -1;

            loop invariant i_26: \forall integer j; 0 <= j < n && visited[j] == 1 ==> dist[j] >= 0;

            loop invariant i_27: \forall integer k; 0 <= k <= rear ==> 0 <= queue[k] < n && visited[queue[k]] == 1 && dist[queue[k]] >= 0;

            loop invariant i_28: \forall integer ii; 0 <= ii < n ==> (visited[ii] == 1 ==> connect(graph, ii, start, n));

            loop invariant i_29: connect(graph, node, start, n);

            loop invariant i_30: \forall integer ii, jj; 0 <= ii < n && 0 <= jj < n ==> graph[ii][jj] == graph[jj][ii];

            loop invariant i_31: \forall integer ii; 0 <= ii < n ==> graph[ii][ii] == 1;

            loop invariant i_32: \forall integer ii, jj; 0 <= ii < n && 0 <= jj < n ==> (graph[ii][jj] == 0 || graph[ii][jj] == 1);


            loop assigns rear;
            loop assigns queue[0..(n)];
            loop assigns dist[0..(n)];
            loop assigns visited[0..(n)];
            loop assigns i;
        */
        for (int i = 0; i < n; i++) {
            if (graph[node][i] == 1 && visited[i] == 0 && rear < n) { 
                rear++;
                queue[rear] = i;
                visited[i] = 1;
                dist[i] = dist[node] + 1;
            }
        }
        front += 1;
        if(front <= rear){
            node = queue[front];
        }
        else{
            break;
        }
    }
}