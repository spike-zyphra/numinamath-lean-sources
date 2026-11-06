import Mathlib

open Real Set
open scoped Real

theorem calculus_22260 : 1 / sin (-120 * π / 180) = -2 * sqrt 3 / 3 := by
  have h1 : -120 * π / 180 = -(2 * π / 3) := by
    ring_nf
  rw [h1]
  have h2 : sin (-(2 * π / 3)) = -sin (2 * π / 3) := by
    rw [sin_neg]
  rw [h2]
  have h3 : sin (2 * π / 3) = sqrt 3 / 2 := by
    have h1 : 2 * π / 3 = π - (π / 3) := by 
      ring_nf
    rw [h1]
    rw [sin_pi_sub]
    have h4 : sin (π / 3) = sqrt 3 / 2 := by 
      exact sin_pi_div_three
    rw [h4]
    <;> ring_nf <;> simp
    <;> ring_nf <;> simp
  rw [h3]
  have h4 : 1 / (- (sqrt 3 / 2 : ℝ)) = -2 * sqrt 3 / 3 := by
    field_simp [show sqrt 3 ≠ 0 by positivity]
    <;> ring_nf <;> 
      field_simp [show sqrt 3 ≠ 0 by positivity, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 3]
  field_simp at h4 ⊢
  <;> nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
  all_goals 
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
  all_goals 
    field_simp [show sqrt 3 ≠ 0 by positivity, Real.sqrt_nonneg (3 : ℝ)]
    <;> nlinarith
    <;> all_goals ring_nf
    <;> all_goals field_simp
    <;> all_goals nlinarith [Real.sqrt_nonneg (3 : ℝ)]
    <;> all_goals tauto