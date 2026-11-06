import Mathlib

theorem inequalities_260176 (a b : ℝ) : a^2 - a * b + b^2 ≥ a * b ↔ b * (b - a) ≥ a * (b - a) := by
  constructor
  · -- Assume $a^2 - ab + b^2 \geq ab$ and prove $b(b-a) \geq a(b-a)$.
    intro h
    nlinarith
  · -- Assume $b(b-a) \geq a(b-a)$ and prove $a^2 - ab + b^2 \geq ab$.
    intro h
    nlinarith [sq_nonneg (a - b)]