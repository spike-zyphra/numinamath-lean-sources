import Mathlib

open Real
open scoped BigOperators

theorem inequalities_249071 (P1 P2 P3 H : ℝ)
  (hP1 : P1 > 0) (hP2 : P2 > 0) (hP3 : P3 > 0)
  (hH : H > 0) (hperp : P1 * P2 + P2 * P3 + P3 * P1 = 0) :
  P1 + P2 + P3 ≥ (9 / 2) * H ^ 2 := by
    nlinarith