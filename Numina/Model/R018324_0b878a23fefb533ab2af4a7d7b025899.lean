import Mathlib

theorem algebra_8534 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)(hx' : x ^ (Real.logb 10 x) * y ^ (Real.logb 10 y) * z ^ (Real.logb 10 z) = 5)

(hy' : x ^ (Real.logb 10 y) * y ^ (Real.logb 10 z) * z ^ (Real.logb 10 x) = Real.sqrt 2) : x * y * z = 10 ∨ x * y * z = 1 / 10 := by
  have h1 : Real.logb 10 (x ^ Real.logb 10 x * y ^ Real.logb 10 y * z ^ Real.logb 10 z) = Real.logb 10 5 := by
    rw [hx']
  have h1' : Real.logb 10 (x ^ Real.logb 10 x * y ^ Real.logb 10 y * z ^ Real.logb 10 z) =
      Real.logb 10 (x ^ Real.logb 10 x) + Real.logb 10 (y ^ Real.logb 10 y) + Real.logb 10 (z ^ Real.logb 10 z) := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    rw [Real.logb_mul (by positivity) (by positivity)]
  have h1'' : Real.logb 10 (x ^ Real.logb 10 x) = Real.logb 10 x * Real.logb 10 x := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith
  have h1''' : Real.logb 10 (y ^ Real.logb 10 y) = Real.logb 10 y * Real.logb 10 y := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith
  have h1'''' : Real.logb 10 (z ^ Real.logb 10 z) = Real.logb 10 z * Real.logb 10 z := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith
  have h1_eq : Real.logb 10 x ^ 2 + Real.logb 10 y ^ 2 + Real.logb 10 z ^ 2 = Real.logb 10 5 := by
    linarith
  have h2 : Real.logb 10 (x ^ Real.logb 10 y * y ^ Real.logb 10 z * z ^ Real.logb 10 x) = Real.logb 10 (Real.sqrt 2) := by
    rw [hy']
  have h2' : Real.logb 10 (x ^ Real.logb 10 y * y ^ Real.logb 10 z * z ^ Real.logb 10 x) =
      Real.logb 10 (x ^ Real.logb 10 y) + Real.logb 10 (y ^ Real.logb 10 z) + Real.logb 10 (z ^ Real.logb 10 x) := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    rw [Real.logb_mul (by positivity) (by positivity)]
  have h2'' : Real.logb 10 (x ^ Real.logb 10 y) = Real.logb 10 y * Real.logb 10 x := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith
  have h2''' : Real.logb 10 (y ^ Real.logb 10 z) = Real.logb 10 z * Real.logb 10 y := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith
  have h2'''' : Real.logb 10 (z ^ Real.logb 10 x) = Real.logb 10 x * Real.logb 10 z := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals linarith
  have h2_eq : Real.logb 10 x * Real.logb 10 y + Real.logb 10 y * Real.logb 10 z + Real.logb 10 x * Real.logb 10 z = Real.logb 10 (Real.sqrt 2) := by
    linarith
  have h3 : Real.logb 10 (Real.sqrt 2) = (1 / 2) * Real.logb 10 2 := by
    have h4 : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h4]
    have h5 : Real.logb 10 ((2 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.logb 10 (2 : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num
    linarith
  rw [h3] at h2_eq
  have h4 : (Real.logb 10 x + Real.logb 10 y + Real.logb 10 z) ^ 2 = 1 := by
    have h5 : (Real.logb 10 x + Real.logb 10 y + Real.logb 10 z) ^ 2 = Real.logb 10 x ^ 2 + Real.logb 10 y ^ 2 + Real.logb 10 z ^ 2 + 2 * (Real.logb 10 x * Real.logb 10 y + Real.logb 10 y * Real.logb 10 z + Real.logb 10 x * Real.logb 10 z) := by
      ring
    rw [h5]
    have h6 : Real.logb 10 5 + Real.logb 10 2 = 1 := by
      have h7 : Real.logb 10 5 + Real.logb 10 2 = Real.logb 10 (5 * 2) := by
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      rw [h7]
      norm_num [Real.logb_eq_iff_rpow_eq]
    nlinarith [h1_eq, h2_eq, h6]
  have h5 : Real.logb 10 x + Real.logb 10 y + Real.logb 10 z = 1 ∨ Real.logb 10 x + Real.logb 10 y + Real.logb 10 z = -1 := by
    have h6 : (Real.logb 10 x + Real.logb 10 y + Real.logb 10 z) ^ 2 = 1 := h4
    have : Real.logb 10 x + Real.logb 10 y + Real.logb 10 z = 1 ∨ Real.logb 10 x + Real.logb 10 y + Real.logb 10 z = -1 := by
      have h8 : (Real.logb 10 x + Real.logb 10 y + Real.logb 10 z) ^ 2 = 1 := h6
      have h9 : Real.logb 10 x + Real.logb 10 y + Real.logb 10 z = 1 ∨ Real.logb 10 x + Real.logb 10 y + Real.logb 10 z = -1 := by
        rw [sq_eq_one_iff] at h8
        tauto
      tauto
    tauto
  cases h5 with
  | inl h6 =>
    have h7 : Real.logb 10 (x * y * z) = 1 := by
      have h8 : Real.logb 10 (x * y * z) = Real.logb 10 x + Real.logb 10 y + Real.logb 10 z := by
        simp [Real.logb_mul, hx.ne.symm, hy.ne.symm, hz.ne.symm]
      rw [h8, h6]
    have h8 : x * y * z = 10 := by
      have h9 : Real.logb 10 (x * y * z) = 1 := h7
      have h10 : x * y * z = (10 : ℝ) ^ (1 : ℝ) := by
        rw [← h9]
        field_simp
      norm_num at h10 ⊢
      linarith
    left
    exact h8
  | inr h6 =>
    have h7 : Real.logb 10 (x * y * z) = -1 := by
      have h8 : Real.logb 10 (x * y * z) = Real.logb 10 x + Real.logb 10 y + Real.logb 10 z := by
        simp [Real.logb_mul, hx.ne.symm, hy.ne.symm, hz.ne.symm]
      rw [h8, h6]
    have h8 : x * y * z = 1 / 10 := by
      have h9 : Real.logb 10 (x * y * z) = -1 := h7
      have h10 : x * y * z = (10 : ℝ) ^ (-1 : ℝ) := by
        rw [← h9]
        field_simp
      norm_num at h10 ⊢
      linarith
    right
    exact h8