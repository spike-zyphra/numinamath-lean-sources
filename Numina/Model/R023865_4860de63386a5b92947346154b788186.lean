import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_155387 {f : ℝ → ℝ} (hf : f = λ x => log (x^2)) :
    DifferentiableOn ℝ f (Set.Ioi 0) := by
  rw [hf]
  apply DifferentiableOn.log
  · -- Show that x ↦ x^2 is differentiable on (0, ∞)
    apply DifferentiableOn.pow
    · -- Show that the identity function is differentiable on (0, ∞)
      apply differentiableOn_id
  all_goals
    intro x hx
    have hx1 : x > 0 := hx
    have hx2 : x ^ 2 > 0 := by
      nlinarith
    all_goals
      try positivity
      try nlinarith