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
        loop invariant i_0: 0 <= front <= rear < n;

        loop invariant i_1: 0 <= node < n;

        loop invariant i_2: queue[0] == start;

        loop invariant i_3: queue[front] == node;

        loop invariant i_4: visited[start] == 1 && dist[start] == 0;

        loop invariant i_5: \forall integer k; 0 <= k <= rear ==> 0 <= queue[k] < n && visited[queue[k]] == 1;

        loop invariant i_6: \forall integer i; 0 <= i < n && visited[i] == 1 ==> dist[i] >= 0;

        loop invariant i_7: \forall integer j; 0 <= j < n && j != start && visited[j] == 0 ==> dist[j] == -1;

        loop invariant i_8: \forall integer i; 0 <= i < n && visited[i] == 1 ==> connect(graph, i, start, n);

        loop invariant i_9: \valid(graph + (0..n));

        loop invariant i_10: \valid(graph[0..n] + (0..n));

        loop invariant i_11: \valid(dist + (0..n));

        loop invariant i_12: \valid(visited + (0..n));

        loop invariant i_13: \valid(queue + (0..n));

        loop invariant i_14: \forall integer i, j; 0 <= i < n && 0 <= j < n ==> graph[i][j] == graph[j][i];

        loop invariant i_15: \forall integer i; 0 <= i < n ==> graph[i][i] == 1;

        loop invariant i_16: \forall integer i, j; 0 <= i < n && 0 <= j < n ==> (graph[i][j] == 0 || graph[i][j] == 1);

        loop invariant i_33: 0 <= front <= rear <= n;

        loop invariant i_45: 0 <= front <= n;

        loop invariant i_46: 0 <= rear <= n;

        loop invariant i_47: front <= rear + 1;

        loop invariant i_48: (front <= rear ==> 0 <= node < n);

        loop invariant i_49: (front <= rear ==> queue[front] == node);

        loop invariant i_50: \forall integer x; 0 <= x < n ==> (visited[x] == 1 ==> dist[x] >= 0);

        loop invariant i_51: \forall integer x; 0 <= x < n ==> (x != start && visited[x] == 0 ==> dist[x] == -1);

        loop invariant i_52: \forall integer x; 0 <= x < n ==> (visited[x] == 1 ==> connect(graph, x, start, n));

        loop invariant i_53: \forall integer a,b; 0 <= a < n && 0 <= b < n ==> graph[a][b] == graph[b][a];

        loop invariant i_54: \forall integer a; 0 <= a < n ==> graph[a][a] == 1;

        loop invariant i_55: \forall integer a,b; 0 <= a < n && 0 <= b < n ==> (graph[a][b] == 0 || graph[a][b] == 1);


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
            loop invariant i_17: 0 <= i <= n;

            loop invariant i_18: 0 <= front <= rear <= n;

            loop invariant i_19: queue[0] == start;

            loop invariant i_20: visited[start] == 1 && dist[start] == 0;

            loop invariant i_21: \forall integer k; 0 <= k <= rear ==> 0 <= queue[k] < n && visited[queue[k]] == 1;

            loop invariant i_22: \forall integer v; 0 <= v < n && visited[v] == 1 ==> dist[v] >= 0;

            loop invariant i_23: \forall integer v; 0 <= v < n && v != start && visited[v] == 0 ==> dist[v] == -1;

            loop invariant i_24: \forall integer v; 0 <= v < n && visited[v] == 1 ==> connect(graph, v, start, n);

            loop invariant i_25: \valid(graph + (0..n));

            loop invariant i_26: \valid(graph[0..n] + (0..n));

            loop invariant i_27: \valid(dist + (0..n));

            loop invariant i_28: \valid(visited + (0..n));

            loop invariant i_29: \valid(queue + (0..n));

            loop invariant i_30: \forall integer a, b; 0 <= a < n && 0 <= b < n ==> graph[a][b] == graph[b][a];

            loop invariant i_31: \forall integer a; 0 <= a < n ==> graph[a][a] == 1;

            loop invariant i_32: \forall integer a, b; 0 <= a < n && 0 <= b < n ==> (graph[a][b] == 0 || graph[a][b] == 1);

            loop invariant i_34: \forall integer i, j; 0 <= i <= n && 0 <= j <= n && i != j ==> \separated(&graph[i] + (0..(n)), &graph[j] + (0..(n)), &dist[0..(n)], &visited[0..(n)], &queue[0..(n)]);

            loop invariant i_35: \separated(&dist[0..(n)], &visited[0..(n)], &queue[0..(n)]);

            loop invariant i_36: 0 <= front <= n;

            loop invariant i_37: 0 <= rear <= n;

            loop invariant i_38: front <= rear + 1;

            loop invariant i_39: \forall integer x; 0 <= x < n ==> (visited[x] == 1 ==> dist[x] >= 0);

            loop invariant i_40: \forall integer x; 0 <= x < n ==> (x != start && visited[x] == 0 ==> dist[x] == -1);

            loop invariant i_41: \forall integer x; 0 <= x < n ==> (visited[x] == 1 ==> connect(graph, x, start, n));

            loop invariant i_42: \forall integer a,b; 0 <= a < n && 0 <= b < n ==> graph[a][b] == graph[b][a];

            loop invariant i_43: \forall integer a,b; 0 <= a < n && 0 <= b < n ==> (graph[a][b] == 0 || graph[a][b] == 1);

            loop invariant i_44: \forall integer p,q; 0 <= p <= n && 0 <= q <= n && p != q ==> \separated(&graph[p] + (0..(n)), &graph[q] + (0..(n)), &dist[0..(n)], &visited[0..(n)], &queue[0..(n)]);

            loop invariant i_56: \forall integer a; 0 <= a < n ==> graph[a][a] == \at(graph[a][a], Pre);


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