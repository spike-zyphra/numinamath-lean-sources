import Mathlib

open Real

theorem algebra_5545 : sqrt (14 + 2 * sqrt 33) = sqrt 11 + sqrt 3 := by
  have h3 : (sqrt 11 + sqrt 3) ^ 2 = 14 + 2 * sqrt 33 := by
    have h31 : (sqrt 11) ^ 2 = 11 := by
      exact sq_sqrt (by norm_num)
    have h32 : (sqrt 3) ^ 2 = 3 := by
      exact sq_sqrt (by norm_num)
    have h33 : sqrt 11 * sqrt 3 = sqrt 33 := by
      calc
        sqrt 11 * sqrt 3 = sqrt (11 * 3) := by
          rw [← Real.sqrt_mul (by norm_num)]
        _ = sqrt 33 := by
          norm_num
    calc
      (sqrt 11 + sqrt 3) ^ 2 = (sqrt 11) ^ 2 + (sqrt 3) ^ 2 + 2 * (sqrt 11 * sqrt 3) := by
        ring
      _ = 11 + 3 + 2 * (sqrt 11 * sqrt 3) := by
        rw [h31, h32]
      _ = 11 + 3 + 2 * (sqrt 33) := by
        rw [h33]
      _ = 14 + 2 * sqrt 33 := by
        ring_nf
  have h4 : (sqrt 11 + sqrt 3) ≥ 0 := by
    have h41 : 0 ≤ sqrt 11 := Real.sqrt_nonneg 11
    have h42 : 0 ≤ sqrt 3 := Real.sqrt_nonneg 3
    linarith
  rw [← h3]
  rw [Real.sqrt_sq]
  linarith [show (sqrt 11 + sqrt 3) ≥ 0 by positivity]