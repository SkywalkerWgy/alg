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
        loop invariant i_0: \forall integer k; i < k <= degree ==> res == poly_val2(coeff, k, degree, x);
        loop invariant i_1: 0 <= i < degree;

        loop assigns i;
        loop assigns res;
    */
    for (int i = degree - 1; i >= 0; i--) {
        res = coeff[i] + x * res;
    }
    return res;
}