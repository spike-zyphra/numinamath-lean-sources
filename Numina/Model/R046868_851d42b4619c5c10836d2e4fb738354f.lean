import Mathlib

open Real Set
open scoped Real

theorem algebra_255686 : cos (π / 5) - sin (π / 10) = 1 / 2 := by
  have h2 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by
    have h2 : cos (π / 5) = (1 + Real.sqrt 5) / 4 := by
      rw [cos_pi_div_five]
    exact h2
  have h3 : sin (π / 10) = (Real.sqrt 5 - 1) / 4 := by
    have h4 : sin (π / 10) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h5 : cos (π / 5) = 1 - 2 * (sin (π / 10) )^2 := by
      have h5 : cos (2 * (π / 10)) = 1 - 2 * (sin (π / 10)) ^ 2 := by
        rw [cos_two_mul]
        rw [sin_sq]
        <;> ring
      have h6 : 2 * (π / 10) = π / 5 := by
        ring_nf
      rw [h6] at h5
      exact h5
    rw [h2] at h5
    have h2v : (sin (π / 10)) ^ 2 = (3 - Real.sqrt 5) / 8 := by
      nlinarith [ h5, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h10 : sin (π / 10) = (Real.sqrt 5 - 1) / 4 := by
      nlinarith [ sq_nonneg (sin (π / 10) - (Real.sqrt 5 - 1) / 4), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h2v, h4, Real.sin_sq_add_cos_sq (π / 10), Real.sin_sq_add_cos_sq (π / 5)]
    exact h10
  rw [h2, h3]
  field_simp
  <;> nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]