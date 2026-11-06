import Mathlib

open Real

theorem inequalities_260116 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b * c) * (b + a * c) ≥ a * b * (c + 1)^2 := by
  nlinarith [sq_nonneg (a * c - b), sq_nonneg (b - a), sq_nonneg (a * c - b * c), sq_nonneg (a - b), sq_nonneg ((a - b) * c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]