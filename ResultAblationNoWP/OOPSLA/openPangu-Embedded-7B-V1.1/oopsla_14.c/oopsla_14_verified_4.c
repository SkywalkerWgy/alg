int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From "The Octagon Abstract Dooopsla_14" HOSC 2006 by Mine.
 */

/*@
    requires m >= 0;
*/
void oopsla_14(int m) {
    int a = 0;
    int j;
    
    // Loop A
    /*@
        loop invariant i_8: j <= m;

        loop invariant i_9: 0 <= a <= m;

        loop invariant i_10: j >= 1 || a == 0;


        loop assigns j;
        loop assigns a;
    */
    for(j = 1; j <= m ; j++){
        if(unknown1()) {
            a++;
        }
        else{
            a--; 
        }
    }

    //@ assert a_1: a>=-m;
    //@ assert a_2: a<=m;
}
