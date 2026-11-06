import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_206552 (r : ℝ) :
  {(x, y) : ℝ × ℝ | ∃ z, z^2 = r^2 - x^2 - y^2 ∧ x + y > 0} =
  {(y, x) : ℝ × ℝ | ∃ z, z^2 = r^2 - y^2 - x^2 ∧ y + x > 0} := by
  ext ⟨x, y⟩
  simp
  <;> tauto