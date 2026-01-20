/*@
    predicate hashtable(int* a, integer length, integer key, integer data) =
        \exists integer i; 0 <= i < length && 
        key == (data + i) % length &&
        a[(data + i) % length] == data && 
        (\forall integer key; 0 <= key < i ==> a[(data + i) % length] != (0 - 1));
*/

//@ lemma mod_property: \forall integer x, y; x > 0 && y > 0 ==> 0 <= x % y < y;

/*@
    requires \valid_read(table+(0..(size - 1)));
    requires size > 0;
    requires data > 0;
    assigns \nothing;
    ensures e_1: \result == -1 || table[\result] == data;
    ensures e_2: ((\result == -1) && (\forall integer i; (data % size) <= i < size ==> table[i] != data)) || \forall integer i; (data % size) <= i < \result ==> table[i] != data;
*/
int _linear_probing_search(int table[], int size, int data) {
    int index = data % size;

    // Loop A
    /*@
        loop invariant i_7: 0 <= index < size;

        loop invariant i_8: index <= size - 1 || index == size;

        loop invariant i_9: index < size || table[index] == data;

        loop invariant i_10: table[index] == data || index >= size;


        loop assigns index;
    */
    while (table[index] != data && index < size) {
        index = index + 1;
    }
    if (index == size) {
        return -1;
    }
    else if (table[index] == data){
        return index;
    }
}