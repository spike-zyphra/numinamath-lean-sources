import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_228513 {f : ℝ → ℝ} (a b : ℝ) (ha : a < b)
  (hf : ContinuousOn f (Set.Icc a b)) (h : f a * f b < 0) :
  ∃ x ∈ Set.Icc a b, f x = 0 := by
  cases mul_neg_iff.mp h with
  | inl h1 => 
    have h4 : 0 ∈ Set.Icc (f b) (f a) := by
      rcases h1 with ⟨h1_left, h1_right⟩
      constructor <;> linarith
    apply intermediate_value_Icc'
    all_goals 
      try trivial
      try linarith
      try exact ha.le
      try tauto
      try nlinarith
      try apply hf
  | inr h2 => 
    have h5 : 0 ∈ Set.Icc (f a) (f b) := by
      rcases h2 with ⟨h2_left, h2_right⟩
      constructor <;> linarith
    apply intermediate_value_Icc
    all_goals 
      try trivial
      try linarith
      try exact ha.le
      try tauto
      try nlinarith
      try apply hf
      all_goals 
        try linarith
        try tauto
        try nlinarith