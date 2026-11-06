import Mathlib


open Real


lemma lemma_1 (x : ℝ) : x^3 = 8 ↔ x = 2 := by
  constructor
  ·
    intro h
    have h1 : x^3 = 8 := h
    have h2 : x^3 - 8 = 0 := by
      linarith
    have h3 : (x - 2) * (x^2 + 2 * x + 4) = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x ^ 2 + 2 * x + 4)]
    cases' (mul_eq_zero.1 h3) with h4 h5
    ·
      linarith
    ·
      have h6 : x ^ 2 + 2 * x + 4 > 0 := by
        have h7 : x ^ 2 + 2 * x + 4 = (x + 1) ^ 2 + 3 := by
          nlinarith
        rw [h7]
        have h8 : (x + 1 : ℝ) ^ 2 ≥ 0 := by
          apply sq_nonneg
        linarith
      nlinarith
  ·
    intro h
    rw [h]
    all_goals norm_num


theorem algebra_20609 (x : ℝ) (hx : 0 < x ∧ x ≠ 1) : Real.logb x 2 + Real.logb x 4 = 3 ↔ x = 2 := by
  constructor
  · -- Assume Real.logb x 2 + Real.logb x 4 = 3, prove x = 2
    intro h
    have h1 : Real.logb x 2 + Real.logb x 4 = Real.logb x (2 * 4) := by 
      rw [← Real.logb_mul (by norm_num) (by norm_num)]
    rw [h1] at h
    -- Real.logb x (2 * 4) = 3
    have h2 : Real.logb x (2 * 4) = 3 := h 
    have h3 : x ^ 3 = 8 := by
      have h4 : Real.logb x (2 * 4) = 3 := h2
      have h5 : x ^ (3 : ℝ) = (2 * 4 : ℝ) := by
        have h6 : x ^ (Real.logb x (2 * 4 : ℝ)) = (2 * 4 : ℝ) := by
          field_simp [Real.rpow_logb, hx.1, hx.2, show (2 * 4 : ℝ) > 0 by norm_num]
        rw [show Real.logb x (2 * 4 : ℝ) = (3 : ℝ) by linarith [h4]] at h6
        norm_num at h6 ⊢
        linarith
      norm_cast at h5
    have hx2 : x = 2 := by
      have h6 : x ^ 3 = 8 := h3
      have h7 : x ^ 3 = 8 := h6
      have h8 : x = 2 := by
        nlinarith [sq_nonneg (x ^ 2 + 2 * x + 4), sq_nonneg (x - 2), sq_nonneg (x + 1)]
      exact h8
    exact hx2
  · -- Assume x = 2, prove Real.logb x 2 + Real.logb x 4 = 3
    intro h
    rw [h]
    have h3 : Real.logb (2 : ℝ) (2 : ℝ) = 1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h4 : Real.logb (2 : ℝ) (4 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith [h3, h4]