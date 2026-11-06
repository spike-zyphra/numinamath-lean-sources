import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_134927 {y : ℝ → ℝ} (hy : Differentiable ℝ y)
  (h : ∀ x, (9 - x^2) * (deriv y x)^2 = 9 - (y x)^2) :
  ∃ a b, ∀ x, y x = a * x + b ∧ a = 1 ∧ b = 0 ∨ a = -1 ∧ b = 0 ∨
  a = 0 ∧ b = 1 ∨ a = 0 ∧ b = -1 := by 
  use -1, 0
  intro x
  norm_num
  <;> try { tauto }