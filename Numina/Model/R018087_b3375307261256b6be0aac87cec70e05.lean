import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_298466 {f : ℝ → ℝ} (hf : f = λ x => x * Real.sin x) :
  Continuous f ∧ Even f := by
  have h1 : Continuous f := by
    rw [hf]
    continuity

  have h2 : Even f := by 
    rw [hf]
    use (fun x => (x * Real.sin x) / 2 )
    funext x
    simp
    all_goals ring

  constructor
  · exact h1
  · exact h2