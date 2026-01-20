#include <stdlib.h>

struct Node {
    char ch;
    int freq;
    struct Node *left;
    struct Node *right;
};

/*@
    predicate Sorted(struct Node **t, integer lo, integer hi) =
        \forall integer i, j; lo <= i <= j < hi ==> t[i]->freq <= t[j]->freq;
*/


/*@
    predicate is_first_second_min(struct Node *t[], int n, int i, int j) =
        0 <= i < n && 0 <= j < n && i != j && \forall integer k; 0 <= k < n ==> t[k]->freq >= t[i]->freq && t[k]->freq >= t[j]->freq;
*/

/*@
  requires freq > 0;
  assigns \nothing;
  ensures \result != \null;
  ensures \result->ch == ch;
  ensures \result->freq == freq;
  ensures \result->left == left && \result->right == right;
*/
struct Node *newNode(char ch, int freq, struct Node *left, struct Node *right) {
    struct Node node;
    node.ch = ch;
    node.freq = freq;
    node.left = left;
    node.right = right;
    struct Node *res = &node;
    return res;
}

/*@ requires \valid(t+(0..n-1));
    requires n > 0;
    requires \forall integer i, j; 0 <= i < n && 0 <= j < n ==> \separated(t[i], t[j]);
    requires \forall integer i; 0 <= i < n ==> t[i]->freq > 0;
    ensures Sorted(t, 0, n-1);
    assigns t[0..n-1];
 */
void insert_sort(struct Node *t[], int n) {
    int i = 1, j = 1;
    struct Node * mv;
    
    /*@
        loop assigns i, j, mv;
        loop assigns t[0..n-1];
        loop invariant 1 <= i <= n;
        loop invariant Sorted(t, 0, i);
        loop variant n - i;
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        /*@
            loop assigns j, t[0..i];
            loop invariant 0 <= j <= i;
            loop invariant j == i ==> Sorted(t, 0, i);
            loop invariant j < i ==> Sorted(t, 0, i+1);
            loop invariant \forall integer k; j <= k < i ==> t[k] > mv;
            loop variant j;
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1]->freq <= mv->freq) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}

/*@
  requires n > 0;
  requires \valid_read(arr+(0..(n - 1)));
  requires \forall integer i, j; 0 <= i < n && 0 <= j < n ==> \separated(arr[i], arr[j]);
  requires Sorted(arr, 0, n);
  requires \forall integer i; 0 <= i < n ==> arr[i]->freq > 0 && arr[i]->left == NULL && arr[i]->right == NULL;
  assigns arr[0..n-1];
  ensures e_1: \result != \null;
*/
struct Node *_huffman(struct Node *arr[], int n) {
    int length = n;
  // Loop A
    /*@
      loop invariant i_0: 0 <= length <= n;


      loop assigns arr[0..n-1];
    */
    while (length > 1) {
        struct Node *node1 = arr[0];
        arr[0] = arr[length - 1];
        length -= 1;
        struct Node *node2 = arr[1];
        struct Node *merged = newNode('\0', node1->freq + node2->freq, node1, node2);
        arr[1] = merged;
        insert_sort(arr, length);
    }
    return arr[0];
}