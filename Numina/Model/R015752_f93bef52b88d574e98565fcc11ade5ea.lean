import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_260592 (k m : ℝ) (a b : ℝ) (h : ∀ x ∈ Icc a b, |x^2 - k * x - m| ≤ 1) :
    b - a ≤ 2 * sqrt 2 := by
  by_contra h1
  push_neg at h1
  -- Set values
  have ha : a ∈ Icc a b := by
    constructor
    · -- Show a ≤ a 
      linarith
    · -- Show a ≤ b 
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0: ℝ) < (2 : ℝ) by norm_num)]
  have hb : b ∈ Icc a b := by 
    constructor
    · -- Show a ≤ b 
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0: ℝ) < (2 : ℝ) by norm_num)]
    · -- Show b ≤ b 
      linarith
  have h3 := h a ha
  have h4 := h b hb
  have h5 : (a + b) / 2 ∈ Icc a b := by 
    constructor 
    · -- Show a ≤ (a + b) / 2 
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0: ℝ) < (2 : ℝ) by norm_num)]
    · -- Show (a + b) / 2 ≤ b 
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0: ℝ) < (2 : ℝ) by norm_num)]
  have h6 := h ((a + b) / 2) h5 
  cases' abs_le.mp h3 with h31 h32
  cases' abs_le.mp h4 with h41 h42
  cases' abs_le.mp h6 with h61 h62
  nlinarith [Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
    sq_nonneg (a - b), sq_nonneg ((a + b) / 2 - a), sq_nonneg ((a + b) / 2 - b), 
    sq_nonneg (a^2 - b^2), sq_nonneg (a - (a + b) / 2), sq_nonneg (b - (a + b) / 2), 
    Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
  ]