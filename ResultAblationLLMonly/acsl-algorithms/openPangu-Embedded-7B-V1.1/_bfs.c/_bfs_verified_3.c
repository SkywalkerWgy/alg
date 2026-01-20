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
        loop invariant i_19: front == 0 && front <= rear && front < n;

        loop invariant i_20: rear == 0 && rear < n;

        loop invariant i_21: \forall integer i; 0 <= i <= rear && (i == node || visited[i] == 0 && dist[i] == dist[node] + 1);

        loop invariant i_22: \forall integer i; 0 <= i <= rear && (i == node || visited[i] == 1);

        loop invariant i_23: \forall integer i; 0 <= i <= rear ==> \exists integer k; 0 <= k <= front && k == queue[front];

        loop invariant i_24: \forall integer i; 0 <= i <= rear ==> \exists integer k; 0 <= k <= n && k == i && graph[node][k] == 1;

        loop invariant i_25: \forall integer i; 0 <= i <= rear && visited[i] == 1 && dist[i] == dist[node] + 1;

        loop invariant i_26: \forall integer i; 0 <= i <= rear ==> i != node;

        loop invariant i_27: \forall integer i; 0 <= i <= rear && i == node;

        loop invariant i_28: \forall integer i; 0 <= i <= rear && visited[i] == 0;

        loop invariant i_29: \forall integer i; 0 <= i <= rear && dist[i] == dist[node] + 1;

        loop invariant i_30: \forall integer i; 0 <= i <= rear && \exists integer k; 0 <= k <= front && k == queue[front];

        loop invariant i_31: \forall integer i; 0 <= i <= rear && \exists integer k; 0 <= k <= n && k == i && graph[node][k] == 1;

        loop invariant i_32: \forall integer i; 0 <= i <= rear && visited[i] == 0 && dist[i] == dist[node] + 1;

        loop invariant i_33: \forall integer i; 0 <= i <= rear && i != node;


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
            loop invariant i_34: front == 0 && front <= rear && front < n;

            loop invariant i_35: rear == 0 && rear < n;

            loop invariant i_36: \forall integer i; 0 <= i <= rear && (i == node || visited[i] == 0 && dist[i] == dist[node] + 1);

            loop invariant i_37: \forall integer i; 0 <= i <= rear && (i == node || visited[i] == 1);

            loop invariant i_38: \forall integer i; 0 <= i <= rear ==> \exists integer k; 0 <= k <= front && k == queue[front];

            loop invariant i_39: \forall integer i; 0 <= i <= rear ==> \exists integer k; 0 <= k <= n && k == i && graph[node][k] == 1;

            loop invariant i_40: \forall integer i; 0 <= i <= rear && visited[i] == 0 && dist[i] == dist[node] + 1;

            loop invariant i_41: \forall integer i; 0 <= i <= rear && i != node;

            loop invariant i_42: \forall integer i; 0 <= i <= rear ==> i != node;

            loop invariant i_43: \forall integer i; 0 <= i <= rear && visited[i] == 0;

            loop invariant i_44: \forall integer i; 0 <= i <= rear && dist[i] == dist[node] + 1;


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