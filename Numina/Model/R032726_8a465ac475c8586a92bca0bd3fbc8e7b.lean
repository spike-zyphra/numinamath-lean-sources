import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_228554
  (f : ℝ → ℝ) (a b : ℝ) (ha : a < b)
  (hf : ContinuousOn f (Set.Icc a b)) :
  Bornology.IsBounded (Set.image f (Set.Icc a b)) := by
  have h1 : a ≤ b := by linarith
  have h2 : IsCompact (Set.Icc a b) := by
    apply isCompact_Icc
  have h3 : IsCompact (Set.image f (Set.Icc a b)) := by
    apply IsCompact.image_of_continuousOn
    all_goals
    try tauto
  have h7 : IsCompact (Set.image f (Set.Icc a b)) := h3
  have h8 : Bornology.IsBounded (Set.image f (Set.Icc a b)) := by
    exact IsCompact.isBounded h7 
  exact h8