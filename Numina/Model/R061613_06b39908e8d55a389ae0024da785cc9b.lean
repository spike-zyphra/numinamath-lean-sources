import Mathlib

theorem algebra_1546 {a b c d e : ℝ} (y : ℝ → ℝ) (hy : y = fun x => a * x ^ 7 + b * x ^ 5 + c * x ^ 3 + d * x + e) (h1 : y 2 = 23) (h2 : y (-2) = -35) : e = -6 := by
  have eq1 : a * 2 ^ 7 + b * 2 ^ 5 + c * 2 ^ 3 + d * 2 + e = 23 := by
    rw [hy] at h1
    exact h1
  have eq2 : a * (-2) ^ 7 + b * (-2) ^ 5 + c * (-2) ^ 3 + d * (-2) + e = -35 := by
    rw [hy] at h2
    exact h2
  norm_num at eq1 eq2 
  linarith