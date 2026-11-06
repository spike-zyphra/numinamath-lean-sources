import Mathlib

open Real

theorem algebra_303359 : (sqrt 2 + sqrt 6) / sqrt (2 + sqrt 3) = 2 := by
  have h1 : sqrt 6 = sqrt 2 * sqrt 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]
    rw [sqrt_mul (by norm_num)]
  have h2 : sqrt 2 + sqrt 6 = sqrt 2 * (1 + sqrt 3) := by
    rw [h1]
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
  have h3 : sqrt (2 + Real.sqrt 3) = (1 + Real.sqrt 3) / Real.sqrt 2 := by
    have h4 : Real.sqrt (2 + Real.sqrt 3) ^ 2 = (2 + Real.sqrt 3) := by
      rw [Real.sq_sqrt]
      positivity
    have h5 : ((1 + Real.sqrt 3) / Real.sqrt 2) ^ 2 = (2 + Real.sqrt 3) := by
      have h6 : ((1 + Real.sqrt 3) / Real.sqrt 2) ^ 2 =
        ((1 + Real.sqrt 3) ^ 2) / (Real.sqrt 2 ^ 2) := by
        field_simp
        <;> nlinarith
      rw [h6]
      have h7 : (1 + Real.sqrt 3) ^ 2 = 1 + 2 * Real.sqrt 3 + (Real.sqrt 3) ^ 2 := by ring
      have h8 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      have h9 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      rw [h7, h8, h9]
      <;> nlinarith
    have h10 : 0 ≤ Real.sqrt (2 + Real.sqrt 3) := by positivity
    have h11 : 0 ≤ (1 + Real.sqrt 3) / Real.sqrt 2 := by
      positivity
    have h12 : Real.sqrt (2 + Real.sqrt 3) = (1 + Real.sqrt 3) / Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (2 + Real.sqrt 3), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3,
        sq_nonneg (Real.sqrt (2 + Real.sqrt 3) - (1 + Real.sqrt 3) / Real.sqrt 2)
      ]
    exact h12
  rw [h2, h3]
  have h4 : 0 ≤ (1 + Real.sqrt 3 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 3]
  have h5 : Real.sqrt 2 ≠ 0 := by
    positivity
  field_simp [h4, h5]
  <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]