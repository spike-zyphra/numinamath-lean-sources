import Mathlib

open Real

theorem inequalities_322203 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (1 + a / 100) * (1 + b / 100) ≤ (1 + (a + b) / 2 / 100) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]