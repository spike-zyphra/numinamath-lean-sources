import Mathlib

theorem algebra_326217 {a b c : ℝ} (h : (b - c)^2 / 4 = (a - b) * (c - a)) (ha : a ≠ 0) :
    (b + c) / a = 2 := by
  have eq1 : (b - c)^2 = 4 * (a - b) * (c - a) := by
    linarith [h]
  
  have eq3 : (b + c) ^ 2 = 4 * a * (b + c - a) := by
    nlinarith [eq1]

  have eq5 : (b + c) / a = 2 := by
    field_simp [ha]
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by assumption), sq_nonneg (b + c - 2 * a)]

  exact eq5