import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_109262
  (a b c : EuclideanSpace ℝ (Fin 3))
  (h₀ : a + b + c = 0)
  (h₁ : ‖a‖ = ‖b‖)
  (h₂ : ‖b‖ = ‖c‖) :
  2 * Real.sin (θ) ∈ Set.Icc (-2) 2 := by 
    constructor
    · -- Show that -2 ≤ 2 * Real.sin (θ)
      linarith [Real.neg_one_le_sin θ]
    · -- Show that 2 * Real.sin (θ) ≤ 2
      linarith [Real.sin_le_one θ]