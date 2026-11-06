import Mathlib

theorem algebra_292958 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ s : Finset ℝ, s.card > 0 ∧ x^2 ∈ s ∨ x * y ∈ s := by 
  use {x * y}
  right
  simp