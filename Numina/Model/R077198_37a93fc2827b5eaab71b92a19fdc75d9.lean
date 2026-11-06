import Mathlib

open Real

theorem inequalities_323974 (a1 a2 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) :
    sqrt (1 + ((a1 + a2) / 2)^2) ≤ (sqrt (1 + a1^2) + sqrt (1 + a2^2)) / 2 := by
  have ha1' : 0 < a1^2 := by nlinarith
  have ha2' : 0 < a2^2 := by nlinarith
  have h1 : 0 < 1 + a1^2 := by nlinarith
  have h2 : 0 < 1 + a2^2 := by nlinarith
  have h3 : 0 < (1 + a1^2) * (1 + a2^2) := by nlinarith

  have h4 : (sqrt (1 + ((a1 + a2) / 2)^2)) ^ 2 = 1 + ((a1 + a2) / 2)^2 := by
    rw [Real.sq_sqrt]
    positivity

  have h5 : ((sqrt (1 + a1^2) + sqrt (1 + a2^2)) / 2) ^ 2 = (sqrt (1 + a1^2) + sqrt (1 + a2^2)) ^ 2 / 4 := by
    ring_nf

  have h6 : ((sqrt (1 + a1^2) + sqrt (1 + a2^2)) / 2) ^ 2 = ( (sqrt (1 + a1^2) ^ 2 + sqrt (1 + a2^2) ^ 2) + 2 * (sqrt (1 + a1^2) * sqrt (1 + a2^2)) ) / 4 := by
    rw [h5]
    have h7 : (sqrt (1 + a1^2) + sqrt (1 + a2^2)) ^ 2 = sqrt (1 + a1^2) ^ 2 + sqrt (1 + a2^2) ^ 2 + 2 * (sqrt (1 + a1^2) * sqrt (1 + a2^2)) := by
      ring_nf
    rw [h7]
    <;> ring

  have h8 : sqrt (1 + a1^2) ^ 2 = 1 + a1^2 := Real.sq_sqrt (by positivity)
  have h9 : sqrt (1 + a2^2) ^ 2 = 1 + a2^2 := Real.sq_sqrt (by positivity)

  have h7 : sqrt (1 + a1^2) * sqrt (1 + a2^2) = sqrt ((1 + a1^2) * (1 + a2^2)) := by
    rw [← Real.sqrt_mul (by positivity)]

  have h10 : (sqrt (1 + ((a1 + a2) / 2) ^ 2)) ^ 2 = 1 + ((a1 + a2) / 2) ^ 2 := h4

  have h11 : ((sqrt (1 + a1^2) + sqrt (1 + a2^2)) / 2) ^ 2 = (2 + a1^2 + a2^2 + 2 * sqrt ((1 + a1^2) * (1 + a2^2)) ) / 4 := by
    rw [h6]
    rw [h8, h9, h7]
    ring_nf <;> norm_num
    <;> ring_nf <;> norm_num

  have h12 : (sqrt (1 + ((a1 + a2) / 2)^2)) ^ 2 ≤ ((sqrt (1 + a1^2) + sqrt (1 + a2^2)) / 2) ^ 2 := by 
    rw [h10, h11]
    nlinarith [sq_nonneg (a1 - a2), Real.sqrt_nonneg ((1 + a1^2) * (1 + a2^2)), Real.sqrt_nonneg (1 + ((a1 + a2) / 2)^2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + ((a1 + a2) / 2)^2) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ ((1 + a1^2) * (1 + a2^2)) by positivity), sq_nonneg (sqrt (1 + a1^2) - sqrt (1 + a2^2)), Real.mul_self_sqrt (show (0 : ℝ) ≤ (1 + a1^2) * (1 + a2^2) by positivity), mul_nonneg (Real.sqrt_nonneg (1 + a1^2)) (Real.sqrt_nonneg (1 + a2^2)), mul_pos (Real.sqrt_pos.mpr h1) (Real.sqrt_pos.mpr h2)]

  nlinarith [Real.sqrt_nonneg (1 + ((a1 + a2) / 2)^2), Real.sqrt_nonneg (1 + a1^2), Real.sqrt_nonneg (1 + a2^2), h4, h12]