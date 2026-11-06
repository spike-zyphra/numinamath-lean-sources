import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_228989 : ∀ x : ℝ, deriv sin x = cos x ∧ deriv cos x = -sin x := by 
  intro x 
  constructor 
  · -- Show that the derivative of sin at x is cos x.
    simp [Real.deriv_sin]
  · -- Show that the derivative of cos at x is -sin x.
    simp [Real.deriv_cos]