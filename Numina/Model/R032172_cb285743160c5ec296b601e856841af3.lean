import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_318609 :
  IsLeast {x | ∃ t : ℝ, x = max (max (t^2 + 1) (Real.cos t)) (2 * t)} 1 := by
  constructor
  · -- Show 1 is in the set.
    use 0
    norm_num [Real.cos_zero]
    all_goals norm_num [Real.cos_zero]
  · -- Show 1 is the least element.
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : max (max (t ^ 2 + 1) (Real.cos t)) (2 * t) ≥ t ^ 2 + 1 := by
      have h2 : max (t ^ 2 + 1) (Real.cos t) ≥ t ^ 2 + 1 := by
        cases max_cases (t ^ 2 + 1) (Real.cos t) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      cases max_cases (max (t ^ 2 + 1) (Real.cos t)) (2 * t) with
      | inl h =>
        linarith
      | inr h =>
        linarith
    have h4 : t ^ 2 + 1 ≥ 1 := by
      nlinarith [sq_nonneg t]
    have h5 : max (max (t^2 + 1) (Real.cos t)) (2 * t) ≥ 1 := by
      linarith [h1, h4]
    linarith [ht, h5]