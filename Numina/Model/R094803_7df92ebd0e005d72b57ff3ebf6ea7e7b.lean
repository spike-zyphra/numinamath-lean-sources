import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_229018 {f g : ℝ → ℝ}
  (hf : f = arcsin) (hg : g = arctan) :
  deriv f = (λ x => 1 / sqrt (1 - x ^ 2)) ∧ deriv g = (λ x => 1 / (1 + x ^ 2)) := by
  constructor
  · -- prove the derivative of arcsin
    rw [hf]
    funext x
    simp [Real.deriv_arcsin]
  · -- prove the derivative of arctan
    rw [hg]
    funext x
    simp [Real.deriv_arctan]