int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on ex3 from NECLA Static Analysis Benchmarks
 */


void oopsla_11(){
    int j = 0;
    int i;
    int x = 100;
    
    // Loop A
    /*@
        loop invariant i_0: j == 2*i;

        loop invariant i_1: 0 <= i <= x;


        loop assigns j;
        loop assigns i;
    */
    for (i = 0; i < x ; i++){
        j = j + 2;
    }

    //@ assert a_1: j == 2*x;
}


