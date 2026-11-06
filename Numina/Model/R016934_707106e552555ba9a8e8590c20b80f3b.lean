import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_147048 (f : ℝ → ℝ) (hf : f = λ θ => sqrt 2 * exp θ) :
    ∫ θ in (0)..(π / 3), sqrt ((deriv f θ)^2 + (f θ)^2) = 2 * (exp (π / 3) - 1) := by
  have f_eq : f = λ θ => sqrt 2 * exp θ := by simp [hf]
  have deriv_f : ∀ θ, deriv f θ = sqrt 2 * exp θ := by
    intro θ
    rw [f_eq]
    simp [deriv_mul, deriv_id'', mul_comm]
  have integrand_simp : ∀ θ, sqrt ((deriv f θ) ^ 2 + (f θ) ^ 2) = 2 * exp θ := by
    intro θ
    have h1 : (deriv f θ) ^ 2 + (f θ) ^ 2 = (4 * (exp θ) ^ 2) := by
      simp [deriv_f, f_eq]
      ring_nf
      <;> norm_num [Real.sq_sqrt]
      <;> ring
    have h2 : sqrt ((deriv f θ) ^ 2 + (f θ) ^ 2) = sqrt (4 * (exp θ) ^ 2) := by
      rw [h1]
    have h3 : sqrt (4 * (exp θ) ^ 2) = 2 * exp θ := by
      have h4 : (4 * (exp θ) ^ 2 : ℝ) = (2 * exp θ) ^ 2 := by
        ring_nf
      rw [h4]
      have h5 : sqrt ((2 * exp θ) ^ 2) = 2 * exp θ := by
        rw [Real.sqrt_sq (by positivity)]
      linarith [h5]
    rw [h2, h3]
  simp_rw [integrand_simp]
  simp [intervalIntegral.integral_const, mul_comm]
  <;> ring_nf <;> norm_num