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
        loop invariant i_0: j == 0 || x == 100;

        loop invariant i_1: j <= 2*x;

        loop invariant i_2: j <= 2*x && i < x;

        loop invariant i_4: j <= 2*x && (j - 2*x) % x == 0;

        loop invariant i_7: j <= 2*x && j % x == 0;

        loop invariant i_8: j <= 2*x && i == 0 || j % x == 0;

        loop invariant i_9: j <= 2*x && (j - 2*x) % x == 0 && i < x;

        loop invariant i_10: j <= 2*x && j % x == 0 && i < x;

        loop invariant i_11: j <= 2*x && i < x && (j - 2*x) % x == 0;

        loop invariant i_12: j <= 2*x && (i == 0 || j % x == 0);

        loop invariant i_13: j == j + 2;

        loop invariant i_14: j == j + 2 && i == 0;


        loop assigns j;
        loop assigns i;
    */
    for (i = 0; i < x ; i++){
        j = j + 2;
    }

    //@ assert a_1: j == 2*x;
}


