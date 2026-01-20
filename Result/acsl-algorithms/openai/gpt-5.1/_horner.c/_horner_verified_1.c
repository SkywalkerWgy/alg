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
        loop invariant i_0: degree > 0;

        loop invariant i_1: \valid_read(coeff+(0..degree));

        loop invariant i_2: -1 <= i <= degree - 1;

        loop invariant i_3: 0 <= i + 1 <= degree;

        loop invariant i_4: res == poly_val2(coeff, i + 1, degree, x);


        loop assigns i;
        loop assigns res;
    */
    for (int i = degree - 1; i >= 0; i--) {
        res = coeff[i] + x * res;
    }
    return res;
}