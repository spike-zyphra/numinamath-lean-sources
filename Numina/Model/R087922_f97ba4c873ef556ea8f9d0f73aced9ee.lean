import Mathlib

theorem algebra_304955 {x y : ℝ} (h : x ≠ 1 ∧ y ≠ 0) :
    ∃ z, 1 / (x - y) = z ↔ x ≠ 1 ∧ y ≠ 0 := by
  use 1 / (x - y)
  simp
  <;> tauto