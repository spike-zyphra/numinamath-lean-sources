import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9377 (f : ℝ → ℝ) (hf : f = λ x => cos (x - π / 8)) :
    IsLeast {y | ∃ x ∈ Icc (π / 6) (2 * π / 3), f x = y} (cos (π *(13/ 24))) := by
  constructor
  · -- Prove cos(13π/24) is in the set.
    use (2 * π / 3)
    constructor
    · -- Show that 2π/3 is in the interval [π/6, 2π/3].
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show that f (2π/3) = cos (π * (13 / 24)).
      rw [hf]
      have h : cos ((2 * π / 3) - π / 8) = cos (π * (13 / 24)) := by 
        ring_nf
      simpa using h
  · -- Prove cos(13π/24) is minimal in the set.
    intro y hy
    rcases hy with ⟨x, hx, hx_eq⟩
    rw [hf] at hx_eq
    simp at hx_eq
    rcases hx with ⟨hx1, hx2⟩
    have h3 : (x - π / 8) ≤ π * (13 / 24) := by 
      linarith
    have h4 : π * (13 / 24) ≤ π := by
      linarith
    have h5 : cos (π * (13 / 24)) ≤ cos (x - π / 8) := by
      have h6 : (x - π / 8) ≤ π * (13 / 24) := by
        linarith
      have h7 : 0 ≤ π * (13 / 24) := by
        linarith [Real.pi_pos]
      have h8 : 0 ≤ x - π / 8 := by 
        linarith [Real.pi_pos]
      have h9 : π * (13 / 24) ≤ π := by
        linarith [Real.pi_pos]
      have h10 : x - π / 8 ≤ π := by 
        linarith [Real.pi_pos]
      apply Real.cos_le_cos_of_nonneg_of_le_pi 
      all_goals 
        linarith
    linarith [hx_eq, h5]