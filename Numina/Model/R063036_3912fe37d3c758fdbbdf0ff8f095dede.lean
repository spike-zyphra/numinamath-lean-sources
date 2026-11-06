import Mathlib

theorem inequalities_195948 (x : ℝ) :
    abs (x + 2000) < abs (x - 2001) ↔ x < 0.5 := by
  constructor
  · -- Forward direction: |x+2000| < |x-2001| → x < 0.5
    intro h
    have h1 : (x + 2000) ^ 2 < (x - 2001) ^ 2 := by
      apply sq_lt_sq.mpr
      exact h
    have h2 : x < (0.5 : ℝ) := by
      nlinarith [sq_nonneg (x - 2000.5), sq_nonneg (x - 0.5)]
    linarith
  · -- Backward direction: x < 0.5 → |x+2000| < |x-2001|
    intro h
    have h1 : (x + 2000) ^ 2 < (x - 2001) ^ 2 := by
      nlinarith [h]
    have h2 : abs (x + 2000) < abs (x - 2001) := by
      apply sq_lt_sq.mp
      linarith
    exact h2