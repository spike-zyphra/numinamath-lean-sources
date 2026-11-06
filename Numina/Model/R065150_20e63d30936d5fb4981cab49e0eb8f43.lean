import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_229543 {f : ℝ → ℝ} (hf : ∃ c, Function.Periodic f c)
  (h : Differentiable ℝ f) :
  ∃ c, Function.Periodic (deriv f) c := by
  rcases hf with ⟨c, hfc⟩
  use 0
  unfold Function.Periodic
  intro x
  simp