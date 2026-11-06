import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_180269 (f : ℝ → ℝ) (hf : f = λ x => (x^2 + x + 1)/(x^2 + 1)) :
    ∀ x, ¬(f x > 3/2) ∧ ¬(f x < 1/2) := by
  intro x 
  have h1 : ¬(f x > 3 / 2) := by 
    have h11 : f x = (x^2 + x + 1) / (x^2 + 1) := by 
      rw [hf]
    intro h
    rw [h11] at h
    have h2 : (x ^ 2 + x + 1) / (x ^ 2 + 1) ≤ 3 / 2 := by 
      have h3 : (x ^ 2 + 1 : ℝ) > 0 := by
        nlinarith [sq_nonneg x]
      apply (div_le_iff₀ h3).mpr 
      nlinarith [sq_nonneg (x - 1)]
    linarith
  have h2 : ¬(f x < 1 / 2) := by 
    have h11 : f x = (x^2 + x + 1) / (x^2 + 1) := by 
      rw [hf]
    intro h
    rw [h11] at h 
    have h4 : (x ^ 2 + x + 1) / (x ^ 2 + 1) ≥ 1 / 2 := by 
      have h3 : (x ^ 2 + 1 : ℝ) > 0 := by
        nlinarith [sq_nonneg x]
      apply (le_div_iff₀ h3).mpr
      nlinarith [sq_nonneg (x + 1)]
    linarith [h4, h]
  exact ⟨h1, h2⟩