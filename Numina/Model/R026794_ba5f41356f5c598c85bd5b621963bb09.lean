import Mathlib

open Real

theorem calculus_22466 {a b : ℝ × ℝ} (ha : a ≠ b) :
    ∃ t, a + t * (a - b) = b + t * (2 * a - 2 * b) ∨
    ∃ t, a + t * (a - b) = (a + b) / 2 + t * (b - a) / 2 ∨
    ∃ t, a + t * (a - b) = b + t / 3 * (2 * a - 2 * b) := by
  use 1
  left
  simp [mul_add, mul_sub, add_mul, sub_eq_add_neg]
  all_goals
    ring_nf