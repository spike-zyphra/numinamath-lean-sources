import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_151469 (f : ℝ → ℝ) (hf : f = λ θ => 6 * sin θ)
  (a b : ℝ) (ha : a = 0) (hb : b = π/3) :
  ∫ θ in (a)..b, sqrt ((deriv f θ)^2 + f θ^2) = 2 * π := by 
  have ha' : a = 0 := ha
  have hb' : b = π / 3 := hb
  rw [ha', hb']
  have h1 : f = λ θ => 6 * sin θ := by exact_mod_cast hf
  have h2 : ∀ θ, deriv f θ = 6 * cos θ := by 
    intro θ
    rw [h1]
    simp [deriv_const_mul, differentiableAt_id', differentiableAt_sin]
    all_goals ring_nf
  have h3 : ∀ θ, sqrt ((deriv f θ) ^ 2 + (f θ) ^ 2) = 6 := by
    intro θ
    rw [h2 θ, h1]
    have h4 : (6 * cos θ : ℝ) ^ 2 + (6 * sin θ : ℝ) ^ 2 = (36 : ℝ) := by
      calc
        (6 * cos θ : ℝ) ^ 2 + (6 * sin θ : ℝ) ^ 2
          = 36 * (cos θ ^ 2 + sin θ ^ 2) := by ring
        _ = 36 * (1:ℝ) := by rw [Real.cos_sq_add_sin_sq θ]
        _ = (36:ℝ) := by ring
    rw [show (6 * cos θ : ℝ) ^ 2 + (6 * sin θ : ℝ) ^ 2 = (36 : ℝ) by linarith [h4]]
    rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
  simp [h3]
  <;> ring_nf <;> field_simp <;> linarith [Real.pi_pos]