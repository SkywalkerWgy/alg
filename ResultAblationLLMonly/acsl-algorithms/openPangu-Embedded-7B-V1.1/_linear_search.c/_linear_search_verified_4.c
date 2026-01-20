/*@ 
  requires n > 0;
  requires \valid(a + (0 .. n-1));
  ensures e_1: \result >= 0 ==> 0 <= \result < n && a[\result] == key;
  ensures e_2: \result < 0 ==> \forall integer j; 0 <= j < n ==> a[j] != key;
*/
int _linear_search(int a[], int n, int key) {
    int ret = -1;
    int i = 0;
    // Loop A
    /*@
        loop invariant i_7: 0 <= i <= n;

        loop invariant i_8: -1 == ret || i == n;


        loop assigns i,ret;
   */
    while (ret == -1 && i < n){
        if (a[i] == key){ 
            ret = i; 
        }
        else { 
            i = i + 1; 
        }
    } 
  return ret;
}