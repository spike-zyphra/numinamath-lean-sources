import Mathlib

theorem inequalities_240343 (x a : ℝ) (hx : 0 < x) (ha : x < a) :
    (a - x)^6 - 3 * a * (a - x)^5 + 5 / 2 * a^2 * (a - x)^4 - 1 / 2 * a^4 * (a - x)^2 < 0 := by 
  have hx1 : 0 < x := hx
  have h2 : 0 < a - x := by linarith
  have h3 : (a - x) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    linarith
  have h4 : x ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    linarith
  have h5 : x ^ 2 - a * x - (1 / 2) * a ^ 2 < 0 := by
    have hx2 : 0 < x := hx1
    have h3 : x < a := by linarith
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos h2, mul_pos hx h2, sq_nonneg (x - a * (1 / 2)), sq_nonneg ((a - x) - a * (1 / 2)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - a * (1 - Real.sqrt 3) / 2), sq_nonneg (x - a * (1 + Real.sqrt 3) / 2), Real.sqrt_nonneg 3, sq_nonneg (x * (a - x)), sq_nonneg (x - a / 2), sq_nonneg ((a - x) - a / 2)]
  have h7 : (a - x) ^ 6 - 3 * a * (a - x) ^ 5 + 5 / 2 * a ^ 2 * (a - x) ^ 4 - 1 / 2 * a ^ 4 * (a - x) ^ 2 =
      (a - x) ^ 2 * x ^ 2 * (x ^ 2 - a * x - (1 / 2) * a ^ 2) := by 
    ring_nf
  rw [h7]
  have h8 : (a - x) ^ 2 * x ^ 2 > 0 := by
    positivity
  nlinarith [h5, mul_pos (show 0 < (a - x) by linarith) (show 0 < x by linarith), sq_nonneg (x - a), sq_nonneg ((a - x) - x / 2), sq_nonneg (a - x - (a / 2))]