import Mathlib

theorem algebra_148537 : (2 * (Real.sqrt 2 + Real.sqrt 6)) / (3 * Real.sqrt (2 + Real.sqrt 3)) = 4 / 3 := by
  have h1 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h2 : Real.sqrt (2 + Real.sqrt 3) = (Real.sqrt 2 + Real.sqrt 6) / 2 := by
    have h2a : ((Real.sqrt 2 + Real.sqrt 6) / 2) ^ 2 = 2 + Real.sqrt 3 := by
      have h3 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := h1
      rw [h3]
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 6, mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3)]
    have h2b : (Real.sqrt 2 + Real.sqrt 6) / 2 ≥ 0 := by
      positivity
    rw [← h2a, Real.sqrt_sq (by
      have h2b : (Real.sqrt 2 + Real.sqrt 6) / 2 ≥ 0 := by
        positivity
      linarith
    )]

  have h3 : Real.sqrt (2 + Real.sqrt 3) = (Real.sqrt 2 + Real.sqrt 6) / 2 := h2

  rw [h3]

  have h4 : Real.sqrt 2 + Real.sqrt 6 > 0 := by
    have h5 : Real.sqrt 2 > 0 := by
      apply Real.sqrt_pos.mpr
      norm_num
    have h6 : Real.sqrt 6 > 0 := by
      apply Real.sqrt_pos.mpr
      norm_num
    linarith

  field_simp [h4]
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]