import Mathlib

theorem inequalities_144150 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a + b)^2 / 2 + (a + b) / 4 ≥ a * Real.sqrt b + b * Real.sqrt a := by
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a - 1 / 2), sq_nonneg (Real.sqrt b - 1 / 2),
    sq_nonneg (a - b), sq_nonneg (Real.sqrt a * 2 - Real.sqrt b * 2), sq_nonneg (Real.sqrt a ^ 2 - Real.sqrt b ^ 2), Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith),
    mul_pos ha hb, 
    Real.sqrt_pos.mpr ha, Real.sqrt_pos.mpr hb, 
    mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb), 
    sq_nonneg (Real.sqrt a - Real.sqrt b), 
    sq_nonneg (a - b), 
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  ]