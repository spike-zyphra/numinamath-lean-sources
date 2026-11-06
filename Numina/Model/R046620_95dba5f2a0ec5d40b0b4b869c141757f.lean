import Mathlib

theorem algebra_1017 {x a : ℝ} (ha : abs x = a) :
  abs (x - a) = a - x := by
  have h1 : a ≥ 0 := by
    have h2 : abs x ≥ 0 := abs_nonneg x
    linarith [ha, h2]

  by_cases h2 : x ≥ 0
  · -- Case where x ≥ 0
    have h3 : abs x = x := abs_of_nonneg h2
    have h4 : a = x := by linarith [ha, h3]
    have h5 : x - a = 0 := by
      linarith [h4]
    rw [h5]
    rw [h4]
    all_goals norm_num
  · -- Case where x < 0
    have h3 : abs x = -x := abs_of_neg (lt_of_not_ge h2)
    have h4 : a = -x := by linarith [ha, h3]
    have h5 : x - a = 2 * x := by
      have h6 : a = -x := h4
      linarith [h6]
    rw [h5]
    have h6 : a - x = -2 * x := by
      have h7 : a = -x := h4
      linarith [h7, show x < 0 by linarith]
    rw [h6]
    have h7 : x < 0 := by linarith
    have h8 : 2 * x < 0 := by linarith
    rw [abs_of_neg h8]
    all_goals ring