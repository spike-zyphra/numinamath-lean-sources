import Mathlib

/-
Problem

The solutions to the equation $x(5x+2) = 6(5x+2)$ are ___.
-/

theorem algebra_9329 (x : ℝ) : x * (5 * x + 2) = 6 * (5 * x + 2) ↔ x = 6 ∨ x = -2 / 5 := by
  constructor
  · -- Forward direction: If x * (5 * x + 2) = 6 * (5 * x + 2), then x = 6 ∨ x = -2/5
    intro h
    by_cases h1 : 5 * x + 2 = 0
    · -- If 5 * x + 2 = 0, then x = -2/5
      right
      linarith
    · -- If 5 * x + 2 ≠ 0, we can divide both sides by (5 * x + 2)
      have h2 : x - 6 = 0 := by
        apply (mul_left_inj' h1).mp
        linarith
      have h3 : x = 6 := by linarith
      left
      exact h3
  · -- Backward direction: If x = 6 ∨ x = -2/5, then x * (5 * x + 2) = 6 * (5 * x + 2)
    rintro (h | h)
    · -- Case x = 6
      rw [h]
    · -- Case x = -2/5
      rw [h]
      norm_num