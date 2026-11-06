import Mathlib

theorem algebra_266288 (x : ℝ) : 2 * Real.cos (x / 2) = 10 ^ x + 10 ^ (-x) + 1 ↔ False := by
  constructor
  · -- Assume $2 \cos \frac{x}{2} = 10^{x} + 10^{-x} + 1$, prove False
    intro h
    have h1 : -1 ≤ Real.cos (x / 2) ∧ Real.cos (x / 2) ≤ 1 := by 
      apply Real.cos_mem_Icc
    have h2 : -2 ≤ 2 * Real.cos (x / 2) ∧ 2 * Real.cos (x / 2) ≤ 2 := by 
      constructor 
      · linarith [h1.1]
      · linarith [h1.2]
    have h3 : (10:ℝ) ^ x + (10:ℝ) ^ (-x) ≥ 2 := by
      have h4 : (10:ℝ) ^ x > 0 := by positivity
      have h5 : (10:ℝ) ^ (-x) > 0 := by positivity
      have h6 : (10:ℝ) ^ x * ((10:ℝ) ^ (-x)) = 1 := by 
        rw [← Real.rpow_add]
        norm_num
        all_goals linarith
      nlinarith [mul_pos h4 h5, sq_nonneg ((10:ℝ) ^ x - 1), sq_nonneg ((10:ℝ) ^ (-x) - 1)]
    have h7 : (10:ℝ) ^ x + (10:ℝ) ^ (-x) + 1 ≥ 3 := by 
      linarith [h3]
    have h8 : 2 * Real.cos (x / 2) ≤ 2 := by 
      linarith [h2.2]
    have h9 : (10 : ℝ) ^ x + (10 : ℝ) ^ (-x) + 1 ≤ 2 := by
      linarith [h, h8]
    linarith
  · -- Assume False, prove $2 \cos \frac{x}{2} = 10^{x} + 10^{-x} + 1$
    intro h
    cases h