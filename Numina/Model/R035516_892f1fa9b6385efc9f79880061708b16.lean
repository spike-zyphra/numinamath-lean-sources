import Mathlib

theorem algebra_13702 {x : ℝ} (hx : 0 < x) :
    Real.logb 2 (6 ^ (Real.logb 2 x)) - Real.logb 2 (x ^ (Real.logb 2 3)) = 8 ↔ x = 256 := by
  constructor
  · -- Forward direction: equation implies x = 256
    intro h
    have h1 : Real.logb 2 (6 ^ (Real.logb 2 x)) = Real.logb 2 x * Real.logb 2 6 := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith
    have h2 : Real.logb 2 (x ^ (Real.logb 2 3)) = Real.logb 2 3 * Real.logb 2 x := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith
    have eq1 : Real.logb 2 (6 ^ (Real.logb 2 x)) - Real.logb 2 (x ^ (Real.logb 2 3)) = Real.logb 2 x * (Real.logb 2 6 - Real.logb 2 3) := by
      rw [h1, h2]
      ring
    rw [eq1] at h
    have h3 : Real.logb 2 6 - Real.logb 2 3 = 1 := by
      have h4 : Real.logb 2 6 = Real.logb 2 (2 * 3) := by norm_num
      rw [h4]
      simp [Real.logb_mul]
      all_goals norm_num
    have h5 : Real.logb 2 x = 8 := by
      rw [h3] at h
      linarith
    have hx2 : x = (2 : ℝ) ^ (8 : ℝ) := by
      rw [←h5]
      field_simp [Real.rpow_logb, show 0 < x by linarith, show 0 < (2 : ℝ) by norm_num, show (2 : ℝ) ≠ 1 by norm_num]
      all_goals linarith
    norm_num at hx2 ⊢
    exact hx2
  · -- Reverse direction: x = 256 implies equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.logb 2 (6 ^ (Real.logb 2 (256 : ℝ))) = Real.logb 2 (256 : ℝ) * Real.logb 2 6 := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
      all_goals linarith
    have h2 : Real.logb 2 ((256 : ℝ) ^ (Real.logb 2 3)) = Real.logb 2 3 * Real.logb 2 (256 : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
      all_goals linarith
    have h3 : Real.logb 2 (256 : ℝ) = 8 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
      <;> linarith
    rw [h1, h2, h3]
    have h4 : Real.logb 2 6 - Real.logb 2 3 = 1 := by
      have h5 : Real.logb 2 6 = Real.logb 2 (2 * 3) := by norm_num
      rw [h5]
      simp [Real.logb_mul]
      all_goals norm_num
    nlinarith [h4]