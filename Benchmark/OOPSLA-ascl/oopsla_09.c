
int unknown1();
int unknown2();
int unknown3();

/*
 * "fragtest_simple" from InvGen benchmark suite
 */

/*@
    requires i == 0;
    requires k == 0;
    ensures k >= 0;
*/
void oopsla_09(int i, int pvlen, int t, int k, int n, int j) {

    /*@
        loop assigns i;
    */
    while (unknown1())
        i = i + 1;
    
    if (i > pvlen) {
        pvlen = i;
    } 
    else {
    }
    i = 0;

    /*@
        loop assigns t, i, k;
    */
    while (unknown2()) {
        t = i;
        i = i + 1;
        k = k + 1;
    }

    while (unknown3());

    j = 0;
    n = i;

    /*@
        loop assigns j, i, k;
    */
    while (1) {
        k = k - 1;
        i = i - 1;
        j = j + 1;
        if (j < n) {
        } 
        else {
            break;
        }
    }
}
