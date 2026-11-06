import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_252829 {f : ℝ → ℝ} (hf : ∀ x, f ((1 - x) / (1 + x)) ≥ x) :
    ∀ x, x ≠ -1 → f x ≥ (1 - x) / (1 + x) := by 
  intro x hx
  have h1 : ∀ (u : ℝ), f ((1 - u) / (1 + u)) ≥ u := hf
  have h2 : f x ≥ (1 - x) / (1 + x) := by
    have eq1 : (1 - ((1 - x) / (1 + x)) ) / (1 + ((1 - x) / (1 + x)) ) = x := by 
      field_simp [(show (1 + x) ≠ 0 by intro h0; apply hx; linarith)]
      <;> ring 
    have h3 : f ((1 - ((1 - x) / (1 + x)) ) / (1 + ((1 - x) / (1 + x)) )) ≥ (1 - x) / (1 + x) := by 
      apply h1
    rw [eq1] at h3 
    linarith
  exact h2