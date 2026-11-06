import Mathlib

/-
  Solve for the set of $x$ in the inequality $x^2 - x - 5 > 3x$.
-/
theorem algebra_9087 (x : ℝ) : x^2 - x - 5 > 3 * x ↔ x > 5 ∨ x < -1 := by
  constructor
  · intro h
    -- move the term 3 * x to the left
    have h : x ^ 2 - 4 * x - 5 > 0 := by linarith
    have : x ^ 2 - 4 * x - 5 = (x - 5) * (x + 1) := by ring
    -- factorization
    rw [this] at h
    -- either (x - 5) > 0 or (x + 1) < 0
    rcases (mul_pos_iff).mp h with _ | _
    left; linarith
    right; linarith
  · rintro (_ | _) <;> nlinarith -- just use `nlinarith` to verify the solution set