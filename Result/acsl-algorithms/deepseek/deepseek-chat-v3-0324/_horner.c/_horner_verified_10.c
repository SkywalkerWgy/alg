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
        loop invariant i_2: res == poly_val2(coeff, i+1, degree, x);
        loop invariant i_3: i >= -1;
        loop invariant i_5: -1 <= i <= degree - 1;
        loop invariant i_6: i <= degree - 1;
        loop invariant i_7: poly_val2(coeff, i+1, degree, x) == res;
        loop invariant i_8: 0 <= i + 1 <= degree;
        loop invariant i_9: 0 <= i <= degree - 1;
        loop invariant i_11: 0 <= \at(i, LoopEntry) <= degree;
        loop invariant i_12: \forall integer k; \at(i, LoopEntry) < k <= degree ==> \at(res, LoopEntry) == poly_val2(coeff, k, degree, x);
        loop invariant i_13: 0 <= i+1 <= degree;
        loop invariant i_14: \forall integer k; i < k <= degree ==> res == coeff[k] + x * poly_val2(coeff, k+1, degree, x);
        loop invariant i_15: \forall integer k; i+1 < k <= degree ==> res == poly_val2(coeff, k, degree, x);
        loop invariant i_16: \forall integer k; i < k <= degree ==> res == poly_val2(coeff, k, degree, x);
        loop invariant i_17: res == coeff[i+1] + x * poly_val2(coeff, i+2, degree, x);

        loop assigns i;
        loop assigns res;
    */
    for (int i = degree - 1; i >= 0; i--) {
        res = coeff[i] + x * res;
    }
    return res;
}