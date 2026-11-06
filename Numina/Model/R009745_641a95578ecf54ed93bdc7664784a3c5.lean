import Mathlib

theorem algebra_14602 (x y : ℝ) (hx : |x - 16 ^ ((1 : ℝ) / 5)| = 3) (hy : |y - 16 ^ ((1 : ℝ) / 5)| = 3) (hxy : x > y):
    x - y = 6 := by
  cases' abs_cases (x - 16 ^ ((1 : ℝ) / 5)) with h1 h1 <;> cases' abs_cases (y - 16 ^ ((1 : ℝ) / 5)) with h2 h2 <;> 
    try linarith
  all_goals nlinarith