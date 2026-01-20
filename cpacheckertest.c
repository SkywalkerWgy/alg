
extern void __assert_fail();

extern int __VERIFIER_nondet_int(void);

void __VERIFIER_assert(int cond) {
  if (!cond) {
    __assert_fail();
  }
}

int min_element(int *a, int n) {
    if (n == 0) {
        // behavior empty: n == 0 => result == 0
        __VERIFIER_assert(0 == 0); // 验证返回值是0
        return 0;
    }
    
    // requires: n >= 0 和 valid(a + (0..n-1)) 由调用者保证
    int min = 0;

    for (int i = 1; i < n; i++) {
        // loop invariant: 0 <= i <= n
        __VERIFIER_assert(0 <= i && i <= n);
        // loop invariant: 0 <= min < n  
        __VERIFIER_assert(0 <= min && min < n);
        
        // 检查当前已知最小值确实是最小的
        for (int k = 0; k < i; k++) {
            __VERIFIER_assert(a[k] <= a[min]);
        }
        
        if (a[min] > a[i]) {
            min = i;
        }
    }
    
    // loop invariant 在循环结束后
    __VERIFIER_assert(0 <= min && min < n);
    
    // 验证最终结果确实是最小元素的索引
    for (int i = 0; i < n; i++) {
        __VERIFIER_assert(a[i] >= a[min]);
    }
    
    // behavior not_empty: 0 <= result < n
    __VERIFIER_assert(0 <= min && min < n);
    
    return min;
}

int min_seq(int *p, int n) {
    // requires: n > 0
    __VERIFIER_assert(n > 0);
    // requires: valid(p + (0..n-1)) 由调用者保证
    
    int min_idx = min_element(p, n);
    int result = p[min_idx];
    
    // ensures: forall i, result <= p[i]
    for (int i = 0; i < n; i++) {
        __VERIFIER_assert(result <= p[i]);
    }
    
    // ensures: exists e, result == p[e]
    int exists = 0;
    for (int e = 0; e < n; e++) {
        if (result == p[e]) {
            exists = 1;
            break;
        }
    }
    __VERIFIER_assert(exists);
    
    return result;
}

int main() {
    int n = 10;
    
    // 创建数组并初始化为非确定性值
    int p[10];
    for (int i = 0; i < n; i++) {
        p[i] = __VERIFIER_nondet_int();
    }
    
    // 验证数组有效性
    // \valid(p + (0..n-1)) - 在C中自动满足对于栈数组
    
    int i = min_seq(p, n);
    
    return 0;
}