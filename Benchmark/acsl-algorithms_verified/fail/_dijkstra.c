#include <limits.h>
#define MAX_VERTICES 100
#define INF INT_MAX

/*@
    requires n > 0;
    requires \valid(graph+(0..n-1));
    requires \forall integer i; 0 <= i < n ==> \valid(graph[i] + (0..n-1));
    requires \valid(dist+(0..n-1));
    requires \valid(parent+(0..n-1));
    requires \valid(visited+(0..n-1));
    requires \forall integer k; 0 <= k < n ==> dist[k] == ((k == start) ? 0 : INF);
    requires \forall integer k; 0 <= k < n ==> parent[k] == -1;
    requires \forall integer k; 0 <= k < n ==> visited[k] == 0;
    assigns dist[0..n-1], parent[0..n-1], visited[0..n-1];
    ensures \forall integer k; 0 <= k < n && visited[k] == 1 ==> dist[k] >= 0;
*/
void dijkstra(int graph[][MAX_VERTICES], int n, int start, int dist[], int parent[], int visited[]) {
    /*@
        loop invariant 0 <= count <= n;
        loop assigns parent[0..n-1], dist[0..n-1], visited[0..n-1];
        loop variant n - count;
    */
    for (int count = 0; count < n; count++) {
        int u = -1;
        /*@
            loop invariant 0 <= i <= n;
            loop invariant (u == -1) || (0 <= u < n && \forall integer k; 0 <= k < i && !visited[k] ==> dist[u] <= dist[k]);
            loop assigns i;
            loop variant n - i;
        */
        for (int i = 0; i < n; i++) {
            if (!visited[i] && (u == -1 || dist[i] < dist[u])) {
                u = i;
            }
        }
        if (u == -1)
            break;
        visited[u] = 1;

        /*@
            loop invariant 0 <= j <= n;
            loop invariant \forall integer k; 0 <= k < j ==> visited[k] == 1 || dist[k] <= INF;
            loop assigns parent[0..n-1], dist[0..n-1];
            loop assigns j;
            loop variant n - j;
        */
        for (int j = 0; j < n; j++) {
            if (!visited[j] && graph[u][j] != 0 && dist[u] != INF && dist[u] + graph[u][j] < dist[j]) {
                dist[j] = dist[u] + graph[u][j];
                parent[j] = u;
            }
        }
    }
}