import Mathlib

theorem algebra_19136 (s : ℝ) (h₀ : s ≠ 0) :
    2 * s ^ 5 / s ^ 3 - 6 * s ^ 2 + 7 * s ^ 3 / s = 3 * s ^ 2 := by
  -- Simplify 2 * s ^ 5 / s ^ 3
  have h1 : 2 * s ^ 5 / s ^ 3 = 2 * s ^ 2 := by
    field_simp [h₀]
    <;> ring
  -- Simplify 7 * s ^ 3 / s
  have h3 : 7 * s ^ 3 / s = 7 * s ^ 2 := by
    field_simp [h₀]
    <;> ring
  rw [h1, h3]
  -- Now simplify the resulting expression
  ring