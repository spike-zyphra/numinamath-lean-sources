import Mathlib

theorem algebra_288281 {x y p : ℝ} (hx : x = 1 + 2^p) (hy : y = 1 + 2^(-p)) :
    y = x / (x - 1) := by
  have eq1 : (2 : ℝ) ^ (-p : ℝ) = 1 / ((2 : ℝ) ^ (p : ℝ)) := by
    rw [Real.rpow_neg]
    all_goals norm_num
  have eq2 : y = 1 + 1 / ((2 : ℝ) ^ (p : ℝ)) := by
    rw [hy, eq1]
  have eq3 : (2 : ℝ) ^ (p : ℝ) = x - 1 := by
    rw [hx]
    all_goals linarith
  have eq4 : y = 1 + 1 / (x - 1) := by
    rw [eq2]
    rw [eq3]
  have eq5 : x - 1 ≠ 0 := by
    by_contra h
    have h1 : x = 1 := by linarith
    rw [h1] at hx
    have h2 : (2 : ℝ) ^ (p : ℝ) = 0 := by linarith
    have h3 : (2 : ℝ) ^ (p : ℝ) > 0 := by positivity
    linarith
  rw [eq4]
  field_simp [eq5]
  <;> nlinarith [sq_pos_of_pos (show (2 : ℝ) ^ (p : ℝ) > 0 by positivity), sq_nonneg (x - 1)]