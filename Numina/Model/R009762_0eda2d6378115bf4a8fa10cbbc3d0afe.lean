import Mathlib

theorem number_theory_4901_1 : 2 * 2 * 2 * 2 * 2 = 32 := by
  --we multiply 2 by itself 5 times:
  norm_num

theorem number_theory_4901_2 : 1 * 2 * 3 * 4 * 5 = 120 := by
  --we calculate the factorial of 5
  norm_num

theorem number_theory_4901_3 : 1 ^ 2 * 2 ^ 2 * 3 ^ 2 * 4 ^ 2 * 5 ^ 2 = 14400 := by
  --we calculate the product of the squares of the first 5 integers
  norm_num

theorem number_theory_4901_4 : 2 ^ 1 * 2 ^ 2 * 2 ^ 3 * 2 ^ 4 * 2 ^ 5 = 32768 := by
  --we calculate 2^1 * 2^2 * 2^3 * 2^4 * 2^5 = 2^(1+2+3+4+5) = 2^15
  norm_num