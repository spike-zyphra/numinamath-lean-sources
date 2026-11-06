import Mathlib

open Real

theorem inequalities_1643 (a1 a2 b1 b2 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (h1 : a1 ≥ a2) (h2 : a1 ≤ b1) (h3 : a1 * a2 ≤ b1 * b2) :
    a1 + a2 ≤ b1 + b2 := by
  have h4 : a2^2 <= a1 * a2 := by nlinarith
  have h5 : a2^2 <= b1 * b2 := by linarith [h3, h4]
  nlinarith [mul_pos ha1 ha2, mul_pos ha1 hb1, mul_pos ha2 hb2, mul_pos hb1 hb2, sq_nonneg (a1 - a2), sq_nonneg (b1 - b2), h3, mul_nonneg (show 0 ≤ a1 - a2 by linarith) (show 0 ≤ b1 - a1 by linarith)]