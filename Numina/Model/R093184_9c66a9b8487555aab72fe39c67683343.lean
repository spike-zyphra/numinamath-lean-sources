import Mathlib

theorem algebra_20344 (x : ℝ) : (x / 3 + x / 4 = 14) ↔ (x = 24) := by 
  constructor
  · -- Assume $\frac{x}{3} + \frac{x}{4} = 14$, prove $x = 24$
    intro h
    linarith
  · -- Assume $x = 24$, prove $\frac{x}{3} + \frac{x}{4} = 14$
    intro h
    rw [h]
    norm_num