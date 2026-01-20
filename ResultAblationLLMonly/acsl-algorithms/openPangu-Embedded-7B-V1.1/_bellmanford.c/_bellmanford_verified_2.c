#include <limits.h>
#define MAX_VERTICES 100
#define INF INT_MAX
struct Edge {
    int u, v, weight;
};

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

    // Loop A
    /*@
        loop invariant i_11: && 1 <= i < n;

        loop invariant i_12: && 0 <= j < e;


        loop assigns dist[0..(n-1)], parent[0..(n-1)], i;
    */
    for (int i = 1; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_13: 1 <= i < n;

            loop invariant i_14: 0 <= j < e;

            loop invariant i_15: \forall integer k; 0 <= k < i ==> parent[k] == -1;

            loop invariant i_16: \forall integer k; 0 <= k < i ==> dist[k] == INF;

            loop invariant i_17: \forall integer k; 0 <= k < i ==> edges[k].u >= 1 && edges[k].v >= 1;

            loop invariant i_18: \forall integer k; 0 <= k < i ==> edges[k].u != start && edges[k].v != start;

            loop invariant i_19: \forall integer k; 0 <= k < i ==> dist[edges[k].v] < dist[i];


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