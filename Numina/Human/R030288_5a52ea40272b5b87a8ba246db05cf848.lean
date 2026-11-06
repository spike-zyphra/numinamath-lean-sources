import Mathlib

/- What is the 20th digit in the decimal expansion for the sum of $\frac{2}{9}$ and $\frac{1}{7}$? -/
theorem algebra_21301 : (Int.floor ((2 / 9 + 1 / 7 : ℚ) * 10 ^ 20)) % 10 = 6 := by norm_num
