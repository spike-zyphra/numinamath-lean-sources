import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_155003 (a b c : ℝ) (x : ℝ) :
  ContinuousAt (λ x => a * x^2 + b * x + c) x := by
    apply ContinuousAt.add
    · -- Show that the function `a * x^2 + b * x` is continuous at x
      apply ContinuousAt.add
      · -- Show that the function `a * x^2` is continuous at x
        apply ContinuousAt.mul
        · -- Show that the function `a` is continuous at x
          exact continuousAt_const
        · -- Show that the function `x^2` is continuous at x
          apply ContinuousAt.pow
          exact continuousAt_id
      · -- Show that the function `b * x` is continuous at x
        apply ContinuousAt.mul
        · -- Show that the function `b` is continuous at x
          exact continuousAt_const
        · -- Show that the function `x` is continuous at x
          exact continuousAt_id
    · -- Show that the function `c` is continuous at x
      exact continuousAt_const