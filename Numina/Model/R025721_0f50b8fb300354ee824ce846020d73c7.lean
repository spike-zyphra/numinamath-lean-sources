import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_598466 (p q : ℝ) (h : ∀ x ∈ Icc 0 1, |sqrt (1 - x^2) - p * x - q| ≤ (sqrt 2 - 1) / 2) :
    p = -1 ∧ q = (1 + sqrt 2) / 2 := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h (sqrt 2 / 2) (by
    have h1 : sqrt 2 ≥ 0 := by positivity
    have h2 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    constructor
    · -- Show that 0 <= sqrt 2 / 2
      nlinarith [Real.sqrt_nonneg 2, h2]
    · -- Show that sqrt 2 / 2 <= 1
      nlinarith [Real.sqrt_nonneg 2, h2]
  )
  -- Simplify h0, h1, h2
  -- Compute sqrt at different points
  have h3 : sqrt (1 - (0:ℝ) ^ 2) = 1 := by 
    norm_num [Real.sqrt_eq_iff_sq_eq]
  have h4 : sqrt (1 - (1:ℝ) ^ 2) = 0 := by 
    norm_num [Real.sqrt_eq_zero]
    all_goals norm_num
  have h5 : sqrt (1 - (sqrt 2 / 2 : ℝ) ^ 2) = sqrt 2 / 2 := by
    have h2 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rw [show (1 - (sqrt 2 / 2 : ℝ) ^ 2) = (1 / 2 : ℝ) by
      nlinarith [h2, Real.sqrt_nonneg 2]
    ]
    have h5 : sqrt (1 / 2 : ℝ) = sqrt 2 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num [Real.sq_sqrt]
      <;> ring
    exact h5
  -- Simplify expressions
  simp [h3] at h0
  simp [h4] at h1
  simp [h5] at h2
  -- Solving system of equations and inequalities
  constructor
  · -- Solving for p
    nlinarith [abs_le.mp h0, abs_le.mp h1, abs_le.mp h2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Solving for q
    nlinarith [abs_le.mp h0, abs_le.mp h1, abs_le.mp h2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  all_goals linarith