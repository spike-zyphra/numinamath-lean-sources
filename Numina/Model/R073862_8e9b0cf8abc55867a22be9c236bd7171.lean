import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_286298 (a b : ℝ) (h₀ : -1 ≤ a + b ∧ a + b ≤ 1) (h₁ : 1 ≤ a - 2 * b ∧ a - 2 * b ≤ 3) :
    -11 / 3 ≤ a + 3 * b ∧ a + 3 * b ≤ 1 := by
  constructor
  · -- Proof of the lower bound: -11/3 ≤ a + 3b
    linarith
  · -- Proof of the upper bound: a + 3b ≤ 1
    linarith