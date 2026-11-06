import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_147066 (f : ℝ → ℝ) (hf : f = λ θ => 5 * exp (5 * θ / 12)) :
    ∫ θ in (0)..(π/3), sqrt ((deriv f θ)^2 + (f θ)^2) = 13 * (exp (5 * π / 36) - 1) := by
  have f_eq : f = λ θ => 5 * exp (5 * θ / 12) := hf
  have fderiv : deriv f = fun θ => (25 / 12) * exp (5 * θ / 12) := by
    funext θ
    rw [f_eq]
    simp [deriv_const_mul, deriv_id'', mul_comm]
    <;> field_simp
    <;> ring_nf <;> norm_num
    <;> field_simp
  have integrand_simp : ∀ θ, sqrt ((deriv f θ) ^ 2 + (f θ) ^ 2) = (65 / 12) * exp (5 * θ / 12) := by
    intro θ
    rw [fderiv, hf]
    have h1 : ((25 / 12) * exp (5 * θ / 12) : ℝ) ^ 2 + (5 * exp (5 * θ / 12) : ℝ) ^ 2 = ((65 / 12) * exp (5 * θ / 12) : ℝ) ^ 2 := by
      ring_nf
      <;> simp [exp_pos]
      <;> ring_nf
      <;> norm_num
    rw [h1]
    have h2 : 0 ≤ ((65 / 12) * exp (5 * θ / 12) : ℝ) := by
      positivity
    rw [Real.sqrt_sq (by linarith)]
    all_goals simp
  simp_rw [integrand_simp]
  have h8 : ∫ θ in (0)..(π / 3), (65 / 12) * exp (5 * θ / 12) = (65 / 5) * (exp (5 * (π / 3) / 12) - 1) := by
    rw [intervalIntegral.integral_const_mul]
    have h9 : ∫ (t : ℝ) in (0)..(π / 3), exp (5 * t / 12) = (12 / 5) * (exp (5 * (π / 3) / 12) - exp (5 * (0 : ℝ) / 12)) := by
      simp [intervalIntegral.integral_const, mul_comm]
      <;> ring_nf
      <;> simp [exp_zero]
      <;> ring_nf <;> norm_num
      <;> field_simp
      <;> ring
      <;> field_simp
      <;> ring_nf
    rw [h9]
    norm_num [exp_zero]
    <;> ring_nf <;> norm_num
  have h7 : exp (5 * (π / 3) / 12) = exp (5 * π / 36) := by
    ring_nf
    <;> norm_num
  rw [h8, h7]
  <;> norm_num
  <;> ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num