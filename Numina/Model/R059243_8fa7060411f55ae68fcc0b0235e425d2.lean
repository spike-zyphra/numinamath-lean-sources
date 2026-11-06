import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_283528 {f g : ℝ → ℝ}
  (hf : f = λ x => arcsin (-x)) (hg : g = λ x => arcsin x) :
  ∀ x, f (-x) = g x ∧ f x = g (-x) := by
  intro x
  rw [hf, hg]
  constructor
  · -- Show that f(-x) = g(x)
    simp [show arcsin (-(-x)) = arcsin x by ring]
  · -- Show that f(x) = g(-x)
    simp [show arcsin (-x) = arcsin (-x) by rfl]