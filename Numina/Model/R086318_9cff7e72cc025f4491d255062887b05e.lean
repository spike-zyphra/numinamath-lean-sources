import Mathlib

open Real

theorem inequalities_213504 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 / 2) * (a + b) ^ 2 + (1 / 4) * (a + b) ≥ a * sqrt b + b * sqrt a := by
  nlinarith [sq_nonneg (sqrt a - 1 / 2), sq_nonneg (sqrt b - 1 / 2),
          sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a + sqrt b),
          Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith),
          Real.sqrt_nonneg a, Real.sqrt_nonneg b,
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]