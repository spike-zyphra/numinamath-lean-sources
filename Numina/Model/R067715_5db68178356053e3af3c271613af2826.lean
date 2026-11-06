import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_147582 (f : ℝ → ℝ) (hf : f = λ φ => 6 * sin φ) :
    ∫ φ in (0)..(π/3), sqrt ((deriv f φ)^2 + (f φ)^2) = 2 * π := by
  have f_def : f = λ φ => 6 * sin φ := hf
  have deriv_f : ∀ φ, deriv f φ = 6 * cos φ := by
    intro φ
    rw [f_def]
    simp [deriv_const_mul, deriv_id', mul_comm]
  have integrand_eq_six : ∀ φ, sqrt ((deriv f φ)^2 + (f φ)^2) = 6 := by
    intro φ
    rw [deriv_f φ]
    rw [f_def]
    have h1 : (6 * cos φ) ^ 2 + (6 * sin φ) ^ 2 = (36 : ℝ) := by
      calc
        (6 * cos φ) ^ 2 + (6 * sin φ) ^ 2 = 36 * (cos φ ^ 2 + sin φ ^ 2) := by ring
        _ = 36 * (1 : ℝ) := by rw [Real.cos_sq_add_sin_sq φ]
        _ = (36 : ℝ) := by norm_num
    rw [h1]
    have h2 : sqrt ((36 : ℝ)) = 6 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h2]
  
  simp_rw [integrand_eq_six]
  simp
  <;> ring_nf <;> field_simp <;> ring