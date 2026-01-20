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
        loop invariant i_7: j == 2 * k + 2 || flag == 0;


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
