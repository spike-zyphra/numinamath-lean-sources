import Mathlib

theorem algebra_300695 {x y : ℝ}
    (hx : x = (3 + 2 * Real.sqrt 2)⁻¹) (hy : y = (3 - 2 * Real.sqrt 2)⁻¹) :
    (x + 1)⁻¹ + (y + 1)⁻¹ = 1 := by

  have h1 : x = 3 - 2 * Real.sqrt 2 := by 
    rw [hx]
    have h2 : (3 + 2 * Real.sqrt 2 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    field_simp [h2]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h3 : y = 3 + 2 * Real.sqrt 2 := by
    rw [hy]
    have h4 : (3 - 2 * Real.sqrt 2 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    field_simp [h4]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  rw [h1, h3]

  have h5 : ((3 - 2 * Real.sqrt 2 : ℝ) + 1) ≠ 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h6 : ((3 + 2 * Real.sqrt 2 : ℝ) + 1) ≠ 0 := by 
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  field_simp [h5, h6]
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_self_nonneg (Real.sqrt 2 - 1), mul_self_nonneg (Real.sqrt 2 + 1)]