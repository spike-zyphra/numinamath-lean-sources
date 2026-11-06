import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_147468 (f : ℝ → ℝ) (hf : f = λ θ => 8 * cos θ) :
    ∫ θ in (0)..(π/4), sqrt ((deriv f θ)^2 + f θ^2) = 2 * π := by
  have f_def : f = λ θ => 8 * cos θ := hf
  have deriv_f : ∀ θ, deriv f θ = -8 * sin θ := by
    intro θ
    rw [f_def]
    simp [deriv_const_mul, differentiableAt_cos]
    all_goals ring
    all_goals norm_num
    all_goals ring

  have integrand_simp : ∀ θ, sqrt ((deriv f θ)^2 + f θ^2) = 8 := by
    intro θ
    have h2 : deriv f θ = -8 * sin θ := deriv_f θ
    have h3 : f θ = 8 * cos θ := by
      rw [f_def]
    rw [h2, h3]
    have h1 : (-8 * sin θ)^2 + (8 * cos θ) ^ 2 = (8 : ℝ) ^ 2 := by
      calc
        (-8 * sin θ)^2 + (8 * cos θ) ^ 2
          = 64 * (sin θ ^ 2 + cos θ ^ 2) := by
            ring_nf
        _ = 64 * (1 : ℝ) := by
          rw [Real.sin_sq_add_cos_sq θ]
        _ = (8 : ℝ) ^ 2 := by
          norm_num
    rw [h1]
    exact Real.sqrt_sq (by norm_num)
  simp_rw [integrand_simp]
  <;> ring_nf <;> field_simp
  <;> ring