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
        loop invariant i_9: cur == \null || (\valid(cur) && (cur->left == \null || cur->left->key <= key) && cur->right == \null || cur->right->key >= key) && BST(cur->left) && BST(cur->right));

        loop invariant i_10: cur == \null || (\valid(cur) && (cur->left == \null || cur->left->key <= key) && cur->right == \null || cur->right->key >= key) && cur->left == \null || cur->left->key <= key && cur->left != \null && cur->right == \null || cur->right->key >= key && cur->right != \null && BST(cur->left) && BST(cur->right));

        loop invariant i_11: cur == cur->left;

        loop invariant i_12: cur == cur->right;


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