#ifndef NULL
#define NULL ((void *)0)
#endif

/*@ requires n >= 0;
    requires \valid(base + (0 .. n-1));
    requires \forall integer k1, integer k2; 0 <= k1 < k2 < n ==> base[k1] < base[k2];

    assigns \nothing;

    ensures e_1: \result == \null ==>
            \forall integer i; 0 <= i < n ==> base[i] != key;
    ensures e_2: \result != \null ==>
            \exists integer i; 0 <= i < n && base[i] == key && \result == (base + i);
*/
int *_binary_search(int base[], int n, int key) {
    int l = 0;
    int h = n - 1;

    // Loop A
    /*@ 
        loop invariant i_5: l <= h;

        loop invariant i_6: 0 <= m >= l && m < h && base[m] != key;

        loop invariant i_7: \forall integer i; 0 <= i < n ==> base[i] != key && i != m;

        loop invariant i_8: \exists integer i; 0 <= i < n && base[i] == key;

        loop invariant i_9: \forall integer i; 0 <= i < n && base[i] == key => l <= m && m >= l && m < h;


        loop assigns l, h;
    */
    while (l <= h) {
        int m = l + (h - l) / 2;
        int val = base[m];

        if (val < key) {
            l = m + 1;
        } else if (val > key) {
            h = m - 1;
        } else {
            return base + m;
        }
    }

    return NULL;
}