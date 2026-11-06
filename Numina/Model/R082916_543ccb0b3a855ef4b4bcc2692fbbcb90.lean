import Mathlib

open Real

theorem inequalities_600812 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * b ≤ (a + b) ^ 2 / 4 := by 
  nlinarith [sq_nonneg (a - b)]