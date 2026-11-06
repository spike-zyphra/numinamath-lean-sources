import Mathlib

open Real

theorem inequalities_217371 (x : ℝ) (hx : x ≥ 1) :
    sqrt (x + sqrt (x + sqrt (x + sqrt (x - 1)))) ≥ sqrt (1 + sqrt 2) := by
  have h1 : x - 1 ≥ 0 := by linarith
  have h2 : sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
  have h3 : x + sqrt (x - 1) ≥ 1 := by
    have h4 : sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
    nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith)]
  have h4 : sqrt (x + sqrt (x - 1)) ≥ 1 := by
    have h5 : x + sqrt (x - 1) ≥ (1 : ℝ) := h3
    have h6 : sqrt (x + sqrt (x - 1)) ≥ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
    have h7 : sqrt (1 : ℝ) = (1 : ℝ) := Real.sqrt_eq_cases.mpr (by norm_num)
    linarith
  have h5 : x + sqrt (x + sqrt (x - 1)) ≥ 2 := by
    have h6 : sqrt (x + sqrt (x - 1)) ≥ (1 : ℝ) := h4
    nlinarith [Real.sqrt_nonneg (x + sqrt (x - 1))]
  have h6 : sqrt (x + sqrt (x + sqrt (x - 1))) ≥ Real.sqrt 2 := by
    have h7 : x + sqrt (x + sqrt (x - 1)) ≥ (2 : ℝ) := h5
    have h8 : sqrt (x + sqrt (x + sqrt (x - 1))) ≥ sqrt (2 : ℝ) := Real.sqrt_le_sqrt (by linarith)
    linarith
  have h7 : x + sqrt (x + sqrt (x + sqrt (x - 1))) ≥ (1 + Real.sqrt 2 : ℝ) := by
    have h8 : sqrt (x + sqrt (x + sqrt (x - 1))) ≥ Real.sqrt 2 := h6
    nlinarith [Real.sqrt_nonneg (x + sqrt (x + sqrt (x - 1))), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h8 : sqrt (x + sqrt (x + sqrt (x + sqrt (x - 1)))) ≥ sqrt (1 + Real.sqrt 2) := by
    have h9 : x + sqrt (x + sqrt (x + sqrt (x - 1))) ≥ (1 + Real.sqrt 2 : ℝ) := h7
    have h10 : sqrt (x + sqrt (x + sqrt (x + sqrt (x - 1)))) ≥ sqrt (1 + Real.sqrt 2) := Real.sqrt_le_sqrt (by linarith)
    linarith
  exact h8