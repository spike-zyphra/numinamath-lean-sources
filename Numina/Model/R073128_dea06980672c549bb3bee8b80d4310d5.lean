import Mathlib

theorem algebra_18618 (x : ℝ) (hx : x ≥ 0) :
    x ^ 2 - 8 * x - 33 ≥ 0 ↔ x ≥ 11 := by
  constructor
  · -- Forward implication: $x^2 - 8x - 33 \geq 0$ implies $x \geq 11$ given $x \geq 0$
    intro h
    nlinarith [sq_nonneg (x - 11), sq_nonneg (x + 3), sq_nonneg (x - 11 + x + 3), sq_nonneg (x - 11 - (x + 3)), hx]
  · -- Backward implication: $x \geq 11$ implies $x^2 - 8x - 33 \geq 0$
    intro h
    nlinarith [sq_nonneg (x - 11), sq_nonneg (x + 3), sq_nonneg (x - 11 + x + 3), sq_nonneg (x - 11 - (x + 3)), hx]