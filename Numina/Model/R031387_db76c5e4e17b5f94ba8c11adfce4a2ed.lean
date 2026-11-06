import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_147521 (f : ℝ → ℝ) (hf : f = λ θ => 6 * cos θ) :
    ∫ θ in (0)..(π/3), sqrt ((deriv f θ)^2 + (f θ)^2) = 2 * π := by

  have f_eq : f = λ θ => 6 * cos θ := by exact hf
  have df : deriv f = fun θ => -6 * sin θ := by
    funext θ
    rw [f_eq]
    simp [deriv_const_mul, differentiableAt_cos]
  have integrand_eq : ∀ θ, sqrt ((deriv f θ)^2 + (f θ)^2) = 6 := by
    intro θ
    have h1 : deriv f θ = -6 * sin θ := by simp [df]
    have h2 : f θ = 6 * cos θ := by simp [f_eq]
    rw [h1, h2]
    have h3 : (-6 * sin θ)^2 + (6 * cos θ)^2 = (36:ℝ) := by
      calc
        (-6 * sin θ)^2 + (6 * cos θ)^2 = 36 * (sin θ)^2 + 36 * (cos θ)^2 := by
          ring
      _ = 36 * ( (sin θ)^2 + (cos θ)^2 ) := by ring
      _ = 36 * 1 := by
        have h4 : (sin θ) ^ 2 + (cos θ) ^ 2 = 1 := by
          exact Real.sin_sq_add_cos_sq θ
        rw [h4]
      _ = 36 := by norm_num
    rw [h3]
    have h4 : Real.sqrt (36:ℝ) = 6 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact h4
  have h5 : ∫ θ in (0)..(π/3), sqrt ((deriv f θ)^2 + (f θ)^2) = ∫ θ in (0)..(π/3), (6:ℝ) := by
    congr
    funext θ
    exact integrand_eq θ
  rw [h5]
  simp
  <;> ring_nf
  <;> field_simp
  <;> ring