import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_21103 :
  IsGreatest {x | ∃ z w : ℂ, ‖z‖ = 2 ∧ ‖w‖ = 5 ∧ x = ‖z + w‖} 7 := by
  constructor
  · -- Show that 7 is in the set
    use 2, 5
    norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
  · -- Show that 7 is the greatest element in the set
    intro x hx
    rcases hx with ⟨z, w, hz, hw, hx⟩
    have h1 : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := by 
      apply norm_add_le
    rw [hz, hw] at h1
    rw [hx]
    linarith