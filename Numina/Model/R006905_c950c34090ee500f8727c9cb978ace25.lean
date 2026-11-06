import Mathlib

theorem algebra_18633 (p : ℝ) : 3 * p - 2 * (p - 4) = 7 * p + 6 ↔ p = 1 / 3 := by
  constructor
  · -- Forward direction: If $3p - 2(p-4) = 7p + 6$, then $p = \frac{1}{3}$
    intro h
    linarith
  · -- Backward direction: If $p = \frac{1}{3}$, then $3p - 2(p-4) = 7p + 6$
    intro hp
    rw [hp]
    norm_num