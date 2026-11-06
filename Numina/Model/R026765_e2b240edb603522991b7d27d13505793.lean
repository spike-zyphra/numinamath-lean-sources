import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_147547 (f : ℝ → ℝ) (hf : f = λ φ => 8 * sin φ)
  (a b : ℝ) (ha : a = 0) (hb : b = π/4) :
  ∫ φ in (a)..b, sqrt ((deriv f φ)^2 + (f φ)^2) = 2 * π := by
  rw [ha, hb]
  have f_eq : f = λ φ => 8 * sin φ := by exact hf

  have df : ∀ φ, deriv f φ = 8 * cos φ := by
    intro φ
    rw [f_eq]
    simp

  have integrand_eq : ∀ φ : ℝ, sqrt ((deriv f φ)^2 + (f φ)^2) = 8 := by
    intro φ
    have h1 : deriv f φ = 8 * cos φ := by
      have h1 : deriv f φ = 8 * cos φ := by
        rw [f_eq]
        simp
      linarith [h1]
    have h2 : f φ = 8 * sin φ := by
      simp [hf]
    have h3 : (deriv f φ)^2 + (f φ)^2 = (8 : ℝ) ^2 := by
      rw [h1, h2]
      have h : (8 * cos φ)^2 + (8 * sin φ)^2 = (8 : ℝ) ^2 := by
        calc
          (8 * cos φ)^2 + (8 * sin φ)^2
              = 64 * (cos φ ^ 2 + sin φ ^ 2) := by
                ring_nf
              _ = 64 * (1) := by
                rw [Real.cos_sq_add_sin_sq φ]
              _ = (8 : ℝ) ^2 := by
                norm_num
      exact h
    have h4 : sqrt ((8 : ℝ) ^2) = (8 : ℝ) := by
      rw [Real.sqrt_sq]
      all_goals linarith
    rw [h3]
    rw [h4]

  have h : ∫ φ in (0 : ℝ)..(π / 4), sqrt ((deriv f φ)^2 + (f φ)^2) = 2 * π := by
    have h5 : ∫ φ in (0 : ℝ)..(π / 4), sqrt ((deriv f φ)^2 + (f φ)^2) =
        ∫ φ in (0 : ℝ)..(π / 4), (8 : ℝ) := by
      congr
      funext φ
      exact integrand_eq φ
    rw [h5]
    simp
    <;> ring_nf <;> field_simp
    all_goals linarith [Real.pi_pos]

  exact h