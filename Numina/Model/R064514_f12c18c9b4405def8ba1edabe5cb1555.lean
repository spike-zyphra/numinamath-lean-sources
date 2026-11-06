import Mathlib

theorem algebra_321513 (a : ℝ) (ha : a ≠ 0) (h : a * 2 ^ 2 - 2 * 2 - a < a * 1 ^ 2 - 2 * 1 - a ∧
    a * 1 ^ 2 - 2 * 1 - a < a * 3 ^ 2 - 2 * 3 - a ∧ a * 3 ^ 2 - 2 * 3 - a < a * 0 ^ 2 - 2 * 0 - a) :
    1 / 2 < a ∧ a < 2 / 3 := by
  obtain ⟨h1, h2, h3⟩ := h
  constructor
  · -- Prove 1/2 < a using the second inequality
    linarith
  · -- Prove a < 2/3 using the first and third inequalities
    linarith