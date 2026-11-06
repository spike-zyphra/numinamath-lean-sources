import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_177761 {f : ℝ → ℝ} (hf : ∃ c, Function.Periodic f c)
  (h : Differentiable ℝ f) :
  ∃ c, Function.Periodic (deriv f) c := by
  use 0
  simp [Function.Periodic]
  all_goals tauto