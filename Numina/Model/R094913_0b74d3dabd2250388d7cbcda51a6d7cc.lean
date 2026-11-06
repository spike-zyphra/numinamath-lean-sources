import Mathlib

theorem algebra_185091 {y : ℝ} (hy : y = (Real.sqrt 3 - 1) / 2) :
    (1 - y) * (y + 2) / (y^2 * (y + 1)^2) = 6 := by
  have h1 : y = (Real.sqrt 3 - 1) / 2 := hy
  have eq1 : (1 - y) * (y + 2) = 3 / 2 := by
    rw [h1]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 1), sq_nonneg (Real.sqrt 3 + 1)]
  have eq2 : y^2 * (y + 1)^2 = 1 / 4 := by
    rw [h1]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 1), sq_nonneg (Real.sqrt 3 + 1)]
  rw [eq1, eq2]
  all_goals
    norm_num
    <;> try { field_simp }
    <;> norm_num