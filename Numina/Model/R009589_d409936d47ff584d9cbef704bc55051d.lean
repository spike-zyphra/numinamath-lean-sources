import Mathlib

theorem algebra_9323 (x : ℝ) :
    2 * x ^ 2 - 3 * x - 2 > 0 ↔ x < -1 / 2 ∨ x > 2 := by
  constructor
  · -- Forward: If $2x^2 - 3x - 2 > 0$, then $x < -\frac{1}{2}$ or $x > 2$
    intro h
    have h1 : (x - 2) * (2 * x + 1) > 0 := by nlinarith
    cases (mul_pos_iff.mp h1) with
    | inl h2 =>
      right
      linarith
    | inr h2 =>
      left
      linarith
  · -- Backward: If $x < -\frac{1}{2}$ or $x > 2$, then $2x^2 - 3x - 2 > 0$
    rintro (h | h)
    · -- Case $x < -\frac{1}{2}$
      have h1 : (x - 2) * (2 * x + 1) > 0 := by nlinarith
      nlinarith
    · -- Case $x > 2$
      have h1 : (x - 2) * (2 * x + 1) > 0 := by nlinarith
      nlinarith