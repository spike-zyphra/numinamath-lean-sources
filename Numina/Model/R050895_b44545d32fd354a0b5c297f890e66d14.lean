import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_22764 :
  IsLeast {x | ∃ z w : ℂ, ‖z‖ = 5 ∧ ‖w‖ = 2 ∧ x = ‖z - w‖} 3 := by
  constructor
  · use 5 * (1 : ℂ), 2 * (1 : ℂ)
    norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  · intro x hx
    rcases hx with ⟨z, w, hz, hw, hx⟩
    have h : ‖z - w‖ ≥ ‖z‖ - ‖w‖ := by
      apply norm_sub_norm_le
    rw [hx] at *
    rw [hz, hw] at h 
    linarith