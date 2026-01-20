#include <limits.h>
#define MAX_VERTICES 100
#define INF INT_MAX
struct Edge {
    int u, v, weight;
};


//   ensures \forall integer i; 0 <= i < n ==> dist[i] >= 0;
//   ensures \forall integer i; 0 <= i < n ==> parent[i] == -1 || (dist[parent[i]] + edges[parent[i]].weight == dist[i]);
/*@
    requires e > 0;
    requires n > 0;
    requires \valid(edges+(0..(e - 1)));
    requires \valid(dist+(0..(n - 1)));
    requires \valid(parent+(0..(n - 1)));
    requires 0 <= start < n;
    requires \forall integer k; 0 <= k < e ==> 0 <= edges[k].u < n && 0 <= edges[k].v < n;
    requires \forall integer k; 0 <= k < n ==> parent[k] == -1;
    requires \forall integer k; 0 <= k < n ==> dist[k] == INF;
    assigns dist[0..(n-1)], parent[0..(n-1)];
*/
int _bellmanford(int n, int e, struct Edge edges[], int start, int dist[], int parent[]) {
    dist[start] = 0;

    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < e ==> 0 <= edges[k].u < n && 0 <= edges[k].v < n;
        loop assigns dist[0..(n-1)], parent[0..(n-1)], i;
    */
    for (int i = 1; i < n; i++) {
        /*@
            loop invariant 0 <= j <= e;
            loop invariant \forall integer k; 0 <= k < e ==> 0 <= edges[k].u < n && 0 <= edges[k].v < n;
            loop assigns dist[0..(n-1)];
            loop assigns parent[0..(n-1)];
            loop assigns j;
        */
        for (int j = 0; j < e; j++) {
            int u = edges[j].u;
            int v = edges[j].v;
            int weight = edges[j].weight;
            if (dist[u] != INF && dist[u] + weight < dist[v]) {
                dist[v] = dist[u] + weight;
                parent[v] = u;
            }
        }
    }

    return 0;
}