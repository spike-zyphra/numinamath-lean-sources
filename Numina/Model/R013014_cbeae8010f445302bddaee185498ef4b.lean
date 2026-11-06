import Mathlib

open Real Set

theorem algebra_313054 (x y : ℝ) (h : x^2 + y^2 / 16 = 1) :
    x * sqrt (2 + y^2) ≤ 9 / 4 := by
  have h1 : 0 ≤ 2 + y ^ 2 := by
    nlinarith [sq_nonneg y]
  have h31 : (sqrt (2 + y ^ 2)) ^ 2 = 2 + y ^ 2 := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : x ^ 2 * (2 + y ^ 2) ≤ 81 / 16 := by
    nlinarith [sq_nonneg (x ^ 2 - 9 / 16), sq_nonneg (y ^ 2 - 9 / 4), sq_nonneg (16 * x ^ 2 + y ^ 2), sq_nonneg x, sq_nonneg y, sq_nonneg (4 * x - y), sq_nonneg (4 * x + y), h]
  have h61 : (x * sqrt (2 + y ^ 2)) ^ 2 ≤ 81 / 16 := by
    have h_eq : (x * sqrt (2 + y ^ 2)) ^ 2 = x^2 * (2 + y ^ 2) := by
      calc
        (x * sqrt (2 + y ^ 2)) ^ 2 = x^2 * (sqrt (2 + y ^ 2) ^ 2) := by
          ring_nf
        _ = x^2 * (2 + y^2) := by
          rw [Real.sq_sqrt]
          positivity
    nlinarith [h_eq, h4]
  have h51 : x * sqrt (2 + y ^ 2) ≤ 9 / 4 := by
    have h11 : (x * sqrt (2 + y ^ 2)) ^ 2 ≤ 81 / 16 := h61
    have h12 : (x * sqrt (2 + y ^ 2)) ≤ Real.sqrt (81 / 16) := by
      apply Real.le_sqrt_of_sq_le
      linarith [h11, show (0 : ℝ) ≤ 81 / 16 by norm_num]
    have h13 : Real.sqrt (81 / 16) = 9 / 4 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      <;> norm_num
    linarith [h13, h12]
  linarith [h51]