import Mathlib

/-
  The solution set of the inequality $|2-3x| \geqslant 4$ is __________.
-/
theorem algebra_9005 (x : ℝ) : abs (2 - 3 * x) ≥ 4 ↔ x ≤ -2 / 3 ∨ x ≥ 2 := by
  -- solve the inequality directly
  constructor
  · intro hx
    have : 2 - 3 * x ≤ -4 ∨ 4 ≤ 2 - 3 * x := by
      exact le_abs'.mp hx
    rcases this with h | h
    · apply Or.inr
      linarith
    · apply Or.inl
      linarith
  · intro hx
    have : 2 - 3 * x ≤ -4 ∨ 4 ≤ 2 - 3 * x := by
      rcases hx with h | h
      · apply Or.inr
        linarith
      · apply Or.inl
        linarith
    exact le_abs'.mpr this
