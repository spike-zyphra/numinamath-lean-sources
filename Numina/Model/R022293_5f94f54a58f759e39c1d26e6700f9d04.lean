import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_217616 {x : ℝ} (hx : ⌊sin x + cos x⌋ = 1) :
    1 ≤ sin x + cos x ∧ sin x + cos x < 2 := by
  have h1 : 1 ≤ sin x + cos x := by
    have h2 : (⌊sin x + cos x⌋ : ℝ) ≤ sin x + cos x := Int.floor_le (sin x + cos x)
    rw [show (⌊sin x + cos x⌋ : ℝ) = (1 : ℝ) by exact_mod_cast hx] at h2
    linarith
  have h3 : sin x + cos x < 2 := by
    have h4 : sin x + cos x < (⌊sin x + cos x⌋ : ℝ) + 1 := Int.lt_floor_add_one (sin x + cos x)
    rw [show (⌊sin x + cos x⌋ : ℝ) = (1 : ℝ) by exact_mod_cast hx] at h4
    linarith
  exact ⟨h1, h3⟩