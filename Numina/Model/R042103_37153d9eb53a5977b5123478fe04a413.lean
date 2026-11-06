import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_320325 (f : ℝ → ℝ) (hf : f = λ x => (x^2 - x + 1)/(x^2 + x + 1)) :
    ∀ x, 1/3 ≤ f x ∧ f x ≤ 3 := by
  intro x
  have hfx : f x = (x^2 - x + 1)/(x^2 + x + 1) := by 
    rw [hf]
  
  constructor
  · -- Show that 1/3 ≤ f x
    rw [hfx]
    have h1 : 0 < x^2 + x + 1 := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    
    apply (le_div_iff₀ h1).mpr
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1 / 2)]
  
  · -- Show that f x ≤ 3
    rw [hfx]
    have h1 : 0 < x^2 + x + 1 := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    
    apply (div_le_iff₀ h1).mpr
    nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]