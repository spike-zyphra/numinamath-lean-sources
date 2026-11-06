import Mathlib

theorem algebra_4110 (a b : ℝ) (_ : a ≠ 0) : ∃ r : ℝ, a / b = r → ∃ r : ℝ, b / a = r := by
  use a / b
  intro h
  refine ⟨b / a, rfl⟩