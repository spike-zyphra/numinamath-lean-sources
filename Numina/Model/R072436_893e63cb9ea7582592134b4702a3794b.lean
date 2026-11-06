import Mathlib

open Real

theorem algebra_180038 (a b : ℝ) (ha : round a + round b = 986) (hb : round a + round b + 1 = 993) :
    round (10 * (a + b)) ≥ 988 := by
  linarith