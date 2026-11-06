import Mathlib

theorem algebra_292451 {a b c x : ℝ} (h : a + b + c = 2 * x) :
    x ^ 2 + (x - a) ^ 2 + (x - b) ^ 2 + (x - c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  have h1 : x ^ 2 + (x - a) ^ 2 + (x - b) ^ 2 + (x - c) ^ 2 =
      4 * x ^ 2 - 2 * x * (a + b + c) + (a ^ 2 + b ^ 2 + c ^ 2) := by
    ring
  rw [h1, h]
  ring