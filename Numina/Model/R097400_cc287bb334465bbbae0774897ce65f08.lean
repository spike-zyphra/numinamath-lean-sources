import Mathlib

theorem algebra_297522 (x : ℝ) (hx : Real.sin x > 0 ∧ Real.cos x > 0)
    (h : Real.logb 10 (Real.sin x) + Real.logb 10 (Real.cos x) = -1) :
    2 * Real.logb 10 (Real.sin x + Real.cos x) = Real.logb 10 6 - Real.logb 10 5 := by
  have h1 : Real.sin x > 0 := hx.1
  have h2 : Real.cos x > 0 := hx.2

  have h3 : Real.logb 10 (Real.sin x * Real.cos x) = -1 := by
    have h4 : Real.logb 10 (Real.sin x * Real.cos x) = Real.logb 10 (Real.sin x) + Real.logb 10 (Real.cos x) := by
      rw [Real.logb_mul (by linarith) (by linarith)]
    rw [h4]
    linarith

  have h4 : Real.sin x * Real.cos x = (1 / 10 : ℝ) := by
    have h5 : Real.sin x * Real.cos x > 0 := mul_pos h1 h2

    have h6 : Real.sin x * Real.cos x = (10 : ℝ) ^ (Real.logb 10 (Real.sin x * Real.cos x : ℝ)) := by
      field_simp [Real.rpow_logb, show (Real.sin x * Real.cos x > 0) by assumption, show ((10 : ℝ) > 1) by norm_num]

    rw [h3] at h6
    rw [h6]

    norm_num

  have h5 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  have h6 : (Real.sin x + Real.cos x) ^ 2 = (6 / 5 : ℝ) := by
    calc
      (Real.sin x + Real.cos x) ^ 2 = Real.sin x ^ 2 + Real.cos x ^ 2 + 2 * (Real.sin x * Real.cos x) := by
        ring
      _ = (Real.sin x ^ 2 + Real.cos x ^ 2) + 2 * (Real.sin x * Real.cos x) := by
        ring
      _ = 1 + 2 * (Real.sin x * Real.cos x) := by
        rw [show Real.sin x ^ 2 + Real.cos x ^ 2 = 1 by linarith [h5]]
      _ = 1 + 2 * (Real.sin x * Real.cos x) := by
        rfl
      _ = 1 + 2 * (1 / 10 : ℝ) := by
        rw [h4]
      _ = (6 / 5 : ℝ) := by
        norm_num

  have h7 : 2 * Real.logb 10 (Real.sin x + Real.cos x) = Real.logb 10 ( (Real.sin x + Real.cos x) ^ 2 ) := by
    simp [Real.logb_pow]
    all_goals linarith

  rw [h7]
  rw [h6]

  have h8 : Real.logb 10 ( (6 / 5 : ℝ) ) = Real.logb 10 6 - Real.logb 10 5 := by
    field_simp [Real.logb_div]
    all_goals norm_num

  rw [h8]

  all_goals norm_num