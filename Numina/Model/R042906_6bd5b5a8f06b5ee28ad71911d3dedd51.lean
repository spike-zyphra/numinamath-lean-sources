import Mathlib
open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_160 {f g : ℝ → ℝ} (a b : ℝ) (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
(hfg : ∀ x ∈ (Set.Icc a b), 0 < g x ∧ g x < f x) :
∃ (k : ℝ), 0 < k ∧ ∀ x ∈ (Set.Icc a b), f x ≥ k * g x := by 
  use 1 
  constructor
  · norm_num
  · intro x hx 
    have h6 : x ∈ Set.Icc a b := hx 
    have h7 : 0 < g x := (hfg x h6).1 
    have h8 : g x < f x := (hfg x h6).2 
    simp 
    all_goals linarith