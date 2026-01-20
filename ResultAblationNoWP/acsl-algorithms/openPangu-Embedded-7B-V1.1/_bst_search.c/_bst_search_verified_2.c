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
        loop invariant i_2: cur == root || cur == null || cur->key == key;

        loop invariant i_3: cur != null && (cur->key >= key || cur->left == null);


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