import Mathlib

theorem algebra_2732 {a b c : ℝ} (habc : b ≠ c) (h : (Real.sqrt 3 + 1) * (a - b) + Real.sqrt 2 * (b - c) = a - c) :
    (a - b) / (b - c) < 0 := by
  have h1 : a - c = (a - b) + (b - c) := by
    ring
  rw [h1] at h
  have h2 : Real.sqrt 3 * (a - b) + (Real.sqrt 2 - 1) * (b - c) = 0 := by
    linarith [h]
  have h3 : Real.sqrt 2 > 1 := by
    have h21 : Real.sqrt 2 > Real.sqrt 1 := by
      apply Real.sqrt_lt_sqrt
      all_goals
        norm_num
    have h22 : Real.sqrt 1 = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith
  have h4 : 1 - Real.sqrt 2 < 0 := by
    linarith
  have h5 : Real.sqrt 3 > 0 := by
    positivity
  have h7 : (b - c) ≠ 0 := by
    intro h'
    apply habc
    linarith
  have h8 : (a - b) / (b - c) = (1 - Real.sqrt 2) / Real.sqrt 3 := by
    have h9 : Real.sqrt 3 * (a - b) = (1 - Real.sqrt 2) * (b - c) := by
      linarith [h2]
    have h17 : (b - c) ≠ 0 := h7
    have h16 : Real.sqrt 3 > 0 := h5
    field_simp [h17, h16]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)]
  rw [h8]
  apply div_neg_of_neg_of_pos
  linarith
  all_goals
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), h4]