import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_599263 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
  (h : x^2 + y^2 + z^2 = 1) :
  x + y + z - x * y * z ≥ 1 ∧
  (x + y + z - x * y * z ≤ 8 * sqrt 3 / 9) := by
  constructor
  · -- Prove that the minimum value of g is 1
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz, mul_nonneg (mul_nonneg hx hy) hz]
  · -- Prove or disprove the inequality
    have h3 : x + y + z ≤ Real.sqrt 3 := by
      have h11 : (x + y + z) ^ 2 ≤ 3 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), h, mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hx hz]
      have h22 : Real.sqrt ((x + y + z) ^ 2) ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by linarith)
      have h33 : Real.sqrt ((x + y + z) ^ 2) = x + y + z := by
        rw [Real.sqrt_sq (show 0 ≤ (x + y + z : ℝ) by positivity)]
      nlinarith [h33, h22]
    have h4 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg ((x + y + z) ^ 2 - 3), sq_nonneg (x * y * z), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz, mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ z by nlinarith), h]