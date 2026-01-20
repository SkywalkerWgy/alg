/*@
    predicate hashtable(int* a, integer length, integer key, integer data) =
        \exists integer i; 0 <= i < length && 
        key == (data + i) % length &&
        a[(data + i) % length] == data && 
        (\forall integer key; 0 <= key < i ==> a[(data + i) % length] != (0 - 1));
*/

//@ lemma mod_property: \forall integer x, y; x > 0 && y > 0 ==> 0 <= x % y < y;

/*@
    requires \valid(table+(0..(size - 1)));
    requires size > 0;
    requires data > 0;
    assigns table[0..(size - 1)];
    ensures e_1: \result == -1 || table[\result] == data;
    ensures e_2: ((\result == -1) && (\forall integer i; (data % size) <= i < size ==> table[i] != -1)) || \forall integer i; (data % size) <= i <= \result ==> table[i] != -1;
*/
int _linear_probing_insert(int table[], int size, int data) {
    int index = data % size;

    // Loop A
    /*@
        loop invariant i_0: index >= data % size;

        loop invariant i_1: index < size;

        loop invariant i_2: \forall integer i; (data % size) <= i < index ==> table[i] != -1;

        loop invariant i_3: data % size <= index < size;

        loop invariant i_4: \forall integer i; data % size <= i < index ==> table[i] != -1;

        loop invariant i_5: table[index] != -1 || index == size;

        loop invariant i_6: data % size <= index <= size;

        loop invariant i_7: index <= size;

        loop invariant i_8: \valid(table+(0..size-1));


        loop assigns index;
    */
    while (table[index] != -1 && index < size) {
        index = index + 1;
    }
    if (index == size) {
        return -1;
    }
    else if (table[index] == -1){
        table[index] = data;
        return index;
    }
}