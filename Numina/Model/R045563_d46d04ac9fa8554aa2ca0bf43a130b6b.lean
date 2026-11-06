import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_186057 {x y : ℝ} (hx : x^2 + y^2 = 1) (hy : y > 0)
  (h : ∫ x in (0)..(3 - sqrt 8), π * (1 - x^2) = 4 * π / 3) :
  x = 3 - sqrt 8 := by
  have h1 : sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : ∫ x in (0)..(3 - sqrt 8), π * (1 - x^2) = π * ((3 - sqrt 8) - (3 - sqrt 8)^3 / 3) := by
    simp [intervalIntegral.integral_const_mul, mul_comm]
    <;> ring_nf
    <;> norm_num
  rw [h2] at h 
  have h3 : 3 - sqrt 8 > 0 := by
    have h8 : sqrt 8 > 0 := by positivity
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (8 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
  have h4 : (3 - sqrt 8) - (3 - sqrt 8)^3 / 3 = 4 / 3 := by
    have h5 : π ≠ 0 := Real.pi_ne_zero
    apply (mul_left_inj' h5).mp 
    linarith
  have h2 : (3 - sqrt 8)^3 - 3 * (3 - sqrt 8) + 4 = 0 := by 
    nlinarith [h4]
  nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num), sq_pos_of_pos hy, sq_nonneg (x + 0), sq_nonneg (y - 0), Real.pi_pos]