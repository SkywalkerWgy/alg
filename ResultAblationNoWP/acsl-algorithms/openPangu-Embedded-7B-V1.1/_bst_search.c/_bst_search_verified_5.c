#include <stddef.h>
#include <stdio.h>

struct Node {
    int key;
    struct Node *left;
    struct Node *right;
};

/*@
    predicate BST{L}(struct Node* t) =
        t == \null || (\valid(t) &&
        (t->left == \null || t->left->key <= t->key) &&
        (t->right == \null || t->right->key >= t->key) &&
        BST(t->left) && BST(t->right));

    logic integer height(struct Node* t) =
        t == \null ? 0 : 1 + \max(height(t->left), height(t->right));
*/

/*@
    requires BST(root);
    assigns \nothing;
    ensures e_1: \result == \null || \result->key == key;
*/
struct Node *_bst_search(struct Node *root, int key) {
    struct Node *cur = root;
    // Loop A
    /*@
        loop invariant i_7: cur != NULL && cur->key != key && (key < cur->key || cur->key < key);

        loop invariant i_8: cur == root || \exists i < i_prev; root->left == cur || root->right == cur;

        loop invariant i_9: \exists integer i; 0 <= i <= i_prev;

        loop invariant i_10: \forall integer i; i == 0 || \at(cur, key) >= key;

        loop invariant i_11: \forall integer i; \at(cur, key) <= key || \at(cur, key) == key;

        loop invariant i_12: \forall integer i; \at(cur, key) >= key || \at(cur, key) <= key;


        loop assigns cur;
    */
    while (cur != NULL && cur->key != key) {
        if (key < cur->key)
            cur = cur->left;
        else
            cur = cur->right;
    }
    return cur;
}