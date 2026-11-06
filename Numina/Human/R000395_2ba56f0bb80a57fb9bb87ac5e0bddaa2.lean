import Mathlib

/-Find the solution set of the inequality $x^{2}-3x-4 > 0$.-/
theorem algebra_9431 (x : ℝ) : x ^ 2 - 3 * x - 4 > 0 ↔ x < -1 ∨ x > 4 := by
-- Factor the quadratic expression
  rw [show x ^ 2 - 3 * x - 4 = (x - 4) * (x + 1) by ring]; simp
-- To find the values of $x$ that satisfy the inequality, we have two cases
  rw [mul_pos_iff]; simp
-- Tactic "linarith" will efficiently handle these cases
  constructor; intro h; cases h; right; linarith
  left; linarith
-- Prove the reversed implication using "linarith"
  intro h; cases h; right; constructor; linarith; linarith
  left; constructor; assumption; linarith