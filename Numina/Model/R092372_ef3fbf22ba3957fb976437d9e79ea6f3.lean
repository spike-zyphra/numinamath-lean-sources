import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_26033 (s t : ℝ) (h₀ : s > 0) (h₁ : t > 0)
  (h₂ : s < t) :
  IsLeast {x | ∃ s t : ℝ, s > 0 ∧ t > 0 ∧ s < t ∧ x = (4 * s ^ 2 + t ^ 2) / (5 * s * t)} (4 / 5) := by 
  constructor 
  · -- Show that 4/5 is achievable
    use 1, 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
  · -- Show that 4/5 is a lower bound
    intro x hx
    rcases hx with ⟨s, t, h0, h1, h2, hx⟩
    have h : (4 * s ^ 2 + t ^ 2) / (5 * s * t) ≥ 4 / 5 := by
      have ht : 5 * s * t > 0 := by positivity
      have h1 : 4 * s ^ 2 + t ^ 2 ≥ 4 * s * t := by
        nlinarith [sq_nonneg (2 * s - t)]
      have h2 : (4 * s ^ 2 + t ^ 2) / (5 * s * t) ≥ 4 / 5 := by
        apply (le_div_iff₀' (by nlinarith)).mpr
        nlinarith
      linarith
    linarith [hx, h]