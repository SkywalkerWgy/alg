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
        loop invariant i_49: s for Loop A in the BFS function: ``` loop invariant 0 <= front <= rear < n;

        loop invariant i_50: 0 <= front <= rear < n;

        loop invariant i_51: front <= rear ==> 0 <= node < n;

        loop invariant i_52: \forall integer i; 0 <= i < n && visited[i] == 1 ==> connect(graph, i, start, n);

        loop invariant i_53: \forall integer i; 0 <= i <= rear ==> visited[queue[i]] == 1;

        loop invariant i_54: \forall integer i; 0 <= i <= rear ==> dist[queue[i]] == (i == 0 ? 0 : dist[queue[i-1]] + 1);

        loop invariant i_55: \forall integer i; 0 <= i < n && visited[i] == 1 ==> dist[i] != -1;

        loop invariant i_56: \forall integer i; 0 <= i < front ==> \forall integer j; 0 <= j < n ==> (graph[queue[i]][j] == 1 ==> visited[j] == 1);

        loop invariant i_57: queue[0] == start;

        loop invariant i_58: visited[start] == 1;


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
            loop invariant i_59: 0 <= i <= n;

            loop invariant i_60: \forall integer j; 0 <= j < i ==> (graph[node][j] == 0 || visited[j] == 1);

            loop invariant i_61: \forall integer j; 0 <= j < i && graph[node][j] == 1 && visited[j] == 0 && rear < n ==> rear == \old(rear) + 1 && queue[rear] == j && visited[j] == 1 && dist[j] == dist[node] + 1;

            loop invariant i_62: \forall integer j; 0 <= j < i && graph[node][j] == 1 && (visited[j] == 1 || rear >= n) ==> rear == \old(rear) && visited[j] == \old(visited[j]);

            loop invariant i_63: \forall integer j; 0 <= j < i && graph[node][j] == 0 ==> rear == \old(rear);

            loop invariant i_64: \forall integer k; 0 <= k <= \old(rear) ==> queue[k] == \old(queue[k]);

            loop invariant i_65: \forall integer k; \old(rear) < k <= rear ==> queue[k] == k - \old(rear) - 1 ? j : \old(queue[k]);

            loop invariant i_66: \forall integer k; 0 <= k < n && visited[k] == 1 ==> connect(graph, k, start, n);

            loop invariant i_67: \forall integer k; 0 <= k <= rear ==> visited[queue[k]] == 1;

            loop invariant i_68: \forall integer k; 0 <= k <= rear ==> dist[queue[k]] == (k == 0 ? 0 : dist[queue[k-1]] + 1);

            loop invariant i_69: \forall integer k; 0 <= k < n && visited[k] == 1 ==> dist[k] != -1;

            loop invariant i_70: \forall integer k; 0 <= k < front ==> \forall integer l; 0 <= l < n ==> (graph[queue[k]][l] == 1 ==> visited[l] == 1);

            loop invariant i_71: queue[0] == start;

            loop invariant i_72: visited[start] == 1;


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