import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_147455 (f : ℝ → ℝ) (hf : f = λ φ => 2 * cos φ) :
    ∫ φ in (0)..(π/6), sqrt ((deriv f φ)^2 + (f φ)^2) = π/3 := by

  have f_def : f = λ φ => 2 * cos φ := hf
  have df : ∀ φ, deriv f φ = -2 * sin φ := by 
    intro φ
    rw [f_def]
    simp [deriv_const_mul, differentiableAt_cos]
  
  have integrand : ∀ φ, sqrt ((deriv f φ)^2 + (f φ)^2) = 2 := by
    intro φ 
    have h1 : deriv f φ = -2 * sin φ := df φ
    have h2 : f φ = 2 * cos φ := by 
      rw [f_def]
    rw [h1, h2]
    have h3 : ((-2 * sin φ) ^ 2 + (2 * cos φ) ^ 2) = (4 : ℝ) := by
      have h4 : sin φ ^ 2 + cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ 
      nlinarith [h4]
    rw [h3]
    have h4 : sqrt ((4 : ℝ) ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact h4
  
  simp_rw [integrand]
  simp
  <;> ring_nf