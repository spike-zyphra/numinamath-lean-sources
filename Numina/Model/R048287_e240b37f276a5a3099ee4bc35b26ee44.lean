import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_324898 (x y : ℝ) (h₀ : x - y + 2 ≤ 0) (h₁ : x ≥ 1) (h₂ : x + y - 7 ≤ 0) :
    9 / 5 ≤ y / x ∧ y / x ≤ 6 := by
  have h3 : x > 0 := by linarith
  have h4 : 9 / 5 ≤ y / x := by
    have h5 : 9 * x ≤ 5 * y := by
      linarith 
    have h6 : 9 / 5 ≤ y / x := by
      apply (le_div_iff₀ (by linarith)).mpr
      linarith
    linarith
  have h7 : y / x ≤ 6 := by
    have h8 : y ≤ 6 * x := by
      linarith 
    have h9 : y / x ≤ 6 := by
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    linarith
  exact ⟨h4, h7⟩