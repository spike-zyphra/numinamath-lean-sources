import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_177804 (x y z : ℝ)
  (h₀ : -1 ≤ 2*x+y-z ∧ 2*x+y-z ≤ 8)
  (h₁ : 2 ≤ x-y+z ∧ x-y+z ≤ 9)
  (h₂ : -3 ≤ x+2*y-z ∧ x+2*y-z ≤ 7) :
  7*x+5*y-2*z ∈ Icc (-6) 47 := by
  have h3 : -1 ≤ 2 * x + y - z := h₀.left
  have h4 : 2 * x + y - z ≤ 8 := h₀.right
  have h5 : 2 ≤ x - y + z := h₁.left
  have h6 : x - y + z ≤ 9 := h₁.right
  have h7 : -3 ≤ x + 2 * y - z := h₂.left
  have h8 : x + 2 * y - z ≤ 7 := h₂.right
  constructor
  · -- Prove -6 ≤ 7 * x + 5 * y - 2 * z
    linarith
  · -- Prove 7 * x + 5 * y - 2 * z ≤ 47
    linarith