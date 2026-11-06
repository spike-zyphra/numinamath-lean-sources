import Mathlib

theorem algebra_9155 (x : ℝ) : (2 / 3 * x - 2 = 4) ↔ (x = 9) := by
  constructor
  · -- Forward direction: Assume $\frac{2}{3} x - 2 = 4$, prove $x = 9$
    intro h
    linarith
  · -- Backward direction: Assume $x = 9$, prove $\frac{2}{3} x - 2 = 4$
    intro h
    rw [h]
    norm_num