import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_22405 :
  IsLeast {x | ∃ z w : ℂ, ‖z‖ = 2 ∧ ‖w‖ = 5 ∧ x = ‖w - z‖} 3 := by
  constructor
  · -- Show 3 is in the set
    use (2 * (1 : ℂ))
    use (5 * (1 : ℂ))
    constructor
    · -- Show ‖2 * (1 : ℂ)‖ = 2
      norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    constructor
    · -- Show ‖5 * (1 : ℂ)‖ = 5
      norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    · -- Show 3 = ‖5 * (1 : ℂ) - 2 * (1 : ℂ)‖
      norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  · -- Show 3 is minimal
    intro x hx
    rcases hx with ⟨z, w, hz, hw, heq⟩
    have h1 : ‖w - z‖ ≥ ‖w‖ - ‖z‖ := by 
      have h2 : ‖w‖ = ‖(w - z) + z‖ := by 
        ring_nf
      have h3 : ‖(w - z) + z‖ ≤ ‖w - z‖ + ‖z‖ := by 
        apply norm_add_le
      linarith [h2, h3]
    have h2 : ‖w - z‖ ≥ 3 := by
      have h3 : ‖w‖ = 5 := hw
      have h4 : ‖z‖ = 2 := hz
      linarith [h1, h3, h4]
    have h3 : x = ‖w - z‖ := by 
      simpa using heq
    linarith [h3, h2]