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
        loop invariant i_3: index < size && index >= 0 && \forall integer i; (data % size) <= i < index ==> table[i] != data;

        loop invariant i_4: \forall integer i; (data % size) <= i < index ==> table[i] != data;

        loop invariant i_6: index < size && index >= 0 && index < size && \forall integer i; (data % size) <= i < index ==> table[i] != data;

        loop invariant i_7: index < size && index >= 0 && index < size;


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