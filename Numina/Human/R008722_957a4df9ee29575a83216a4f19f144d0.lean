import Mathlib

/- The value of the expression  \[(2^{1004}+5^{1005})^2-(2^{1004}-5^{1005})^2\]is $k\cdot10^{1004}$ for some positive integer $k$. What is $k$? -/
theorem algebra_12580 (k : ℤ) (kpos : k > 0) (h : (2 ^ 1004 + 5 ^ 1005)^2 - (2 ^ 1004 - 5 ^ 1005)^2 = k * 10 ^ 1004) : k = 20 := by omega
