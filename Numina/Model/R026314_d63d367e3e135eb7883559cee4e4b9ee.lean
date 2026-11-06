import Mathlib

open Real

theorem inequalities_601764 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b + c) ^ 2 / 3 ≥ a * sqrt (b * c) + b * sqrt (c * a) + c * sqrt (a * b) := by 
  have h1 : 0 ≤ b * c := mul_nonneg hb hc
  have h2 : 0 ≤ c * a := mul_nonneg hc ha
  have h3 : 0 ≤ a * b := mul_nonneg ha hb
  have h4 : sqrt (b * c) = Real.sqrt b * Real.sqrt c := by
    rw [Real.sqrt_mul (by linarith [hb, hc])]
  have h5 : sqrt (c * a) = Real.sqrt c * Real.sqrt a := by 
    rw [Real.sqrt_mul (by linarith [hc, ha])]
  have h6 : sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul (by linarith [ha, hb])]
  rw [h4, h5, h6]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a - Real.sqrt c), sq_nonneg (Real.sqrt b - Real.sqrt c),
    Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith),
    sq_nonneg (a * (Real.sqrt b - Real.sqrt c) + b * (Real.sqrt c - Real.sqrt a) + c * (Real.sqrt a - Real.sqrt b)),
    Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c),
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c),
    mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc,
    mul_nonneg (show 0 ≤ Real.sqrt a by positivity) (show 0 ≤ Real.sqrt b by positivity), 
    mul_nonneg (show 0 ≤ Real.sqrt a by positivity) (show 0 ≤ Real.sqrt c by positivity),
    mul_nonneg (show 0 ≤ Real.sqrt b by positivity) (show 0 ≤ Real.sqrt c by positivity)]