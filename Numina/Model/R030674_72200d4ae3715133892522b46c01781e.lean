import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_22126 {a : ℝ} (ha : ∀ x, x ≥ a → a * x ^ 2 ≥ a * x + 2 * a)
  (ha' : ∀ x, x < a → a * x + 2 * a ≥ a * x ^ 2) :
  a ≤ 2 := by 
    by_contra h
    push_neg at h
    have h1 := ha' (-2) (by nlinarith)
    nlinarith