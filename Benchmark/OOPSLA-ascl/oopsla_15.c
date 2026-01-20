int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * from Invgen test suite
 */

/*@
    requires n > 0;
    requires k > n;
    ensures e_1: k >= 0;
*/
void oopsla_15(int n, int k, int i, int j) {
    j = 0;
    
    /*@
        loop assigns k;
        loop assigns j;
    */
    while( j < n ) {
        j++;
        k--;
    } 
}
