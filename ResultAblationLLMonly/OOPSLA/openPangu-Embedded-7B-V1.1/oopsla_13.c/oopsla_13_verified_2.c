int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on "Property-Directed Incremental Invariant Generation" by Bradley et al.
 */

void oopsla_13(int flag) {
    int j = 2; 
    int k = 0;

    // Loop A
    /*@
        loop invariant i_2: k >= 0 && flag == 0 ==> j == 2 * k + 2;

        loop invariant i_3: flag == 0;

        loop invariant i_4: k >= 0;

        loop invariant i_5: flag == 0 && j == 2 * k + 2;

        loop invariant i_6: k != 0 || flag == 1;


        loop assigns j, k;
    */
    while(unknown1()){ 
        if (flag)
            j = j + 4;
        else {
            j = j + 2;
            k = k + 1;
        }
    }

    //@ assert  a_1:  k != 0 ==> j == 2 * k + 2;
}
