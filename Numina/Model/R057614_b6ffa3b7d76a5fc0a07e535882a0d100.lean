import Mathlib

open Real

theorem inequalities_247393 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 2 / 2 + (a + b) / 4 ≥ a * sqrt b + b * sqrt a := by 
  have h1 : 0 ≤ sqrt b := by positivity
  have h2 : 0 ≤ sqrt a := by positivity
  nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a - 1 / 2), sq_nonneg (sqrt b - 1 / 2),
          sq_nonneg (sqrt a + sqrt b - 1 / 2), sq_nonneg (sqrt a * sqrt b - 1 / 4),
          Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith),
          Real.sqrt_nonneg b, Real.sqrt_nonneg a, 
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
          sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a + sqrt b),
          sq_nonneg (a - b)]