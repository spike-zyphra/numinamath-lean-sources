import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_140624 {f g : ℝ → ℝ}
  (hf : f = λ x => x^4 + 3 * x + 5)
  (hg : g = λ x => x^2 * Real.sin x - x^2 / (x^2 + 3)) :
  Continuous f ∧ Continuous g := by
  constructor
  · -- Show that f is continuous
    rw [hf]
    continuity
  · -- Show that g is continuous
    rw [hg]
    apply Continuous.sub
    · -- Show that x^2 * sin x is continuous
      apply Continuous.mul
      · -- Show that x^2 is continuous
        continuity
      · -- Show that sin x is continuous
        apply Real.continuous_sin
    · -- Show that x^2/(x^2+3) is continuous
      apply Continuous.div
      · -- Show that x^2 is continuous
        continuity
      · -- Show that x^2+3 is continuous
        continuity
      all_goals
        intro x
        have h1 : x ^ 2 + 3 > (0 : ℝ) := by
          nlinarith [sq_nonneg x]
        simp [h1]
        all_goals norm_num
        all_goals nlinarith