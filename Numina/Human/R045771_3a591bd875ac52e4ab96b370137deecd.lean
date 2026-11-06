import Mathlib

/-The sum of two numbers S. Suppose 3 is added to each number and then
each of the resulting numbers is doubled. What is the sum of the final two
numbers?
(A) 2S+3 (B) 3S+2 (C) 3S+6 (D) 2S+6 (E) 2S+12
-/
theorem algebra_1116 (a b S : ℕ) (h : a + b = S)
: (2 * (3 + a)) + (2 * (3 + b)) = 12 + 2 * S := by
calc
  (2 * (3 + a)) + (2 * (3 + b))
  _ = (6 + 2 * a) + (6 + 2 * b) := by ring -- we expand the expression using the ring tactic
  _ = 12 + (a * 2) + (b * 2) := by ring -- we rearrange the expression using the ring tactic
  _ = 12 + (2 * a + 2 * b) := by ring -- grouping like terms using the ring tactic
  _ = 12 + 2 * (a + b) := by rw [← mul_add] -- distributivity over multiplication
  _ = 12 + 2 * S := by rw [h]
/-
The answer is E in the choices
-/