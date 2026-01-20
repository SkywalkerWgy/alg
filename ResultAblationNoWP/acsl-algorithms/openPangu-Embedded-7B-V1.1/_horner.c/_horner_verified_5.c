/*@
  logic real poly_val2(int* coeff, integer i, integer degree, real x) =
    i > degree ? 0.0 : coeff[i] + x * poly_val2(coeff, i + 1, degree, x);
*/

/*@
  requires degree > 0;
  requires \valid_read(coeff+(0..degree));
  ensures e_1: \result == poly_val2(coeff, 0, degree, x);
*/
int _horner(int coeff[], int degree, int x) {
    int res = coeff[degree];
    // Loop A
    /*@
        loop invariant i_8: \exists integer k; 0 <= k < i && res == coeff[i] + x^i;

        loop invariant i_9: i >= 0;

        loop invariant i_10: \forall integer p; 0 <= p < \at(k, End_l) ==> coeff[p] + x * res == coeff[i] + x^i;


        loop assigns i;
        loop assigns res;
    */
    for (int i = degree - 1; i >= 0; i--) {
        res = coeff[i] + x * res;
    }
    return res;
}