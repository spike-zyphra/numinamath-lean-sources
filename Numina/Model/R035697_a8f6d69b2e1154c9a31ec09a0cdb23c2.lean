import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_181607 (p q : ℝ) (h : 0 ≤ 2 * p - q ∧ 0 ≤ 3 * q - 2 * p ∧ 0 ≤ 6 - 2 * q) :
    sqrt (2 * p - q) + sqrt (3 * q - 2 * p) + sqrt (6 - 2 * q) ≤ 3 * sqrt 2 := by
  have h1 : 0 ≤ 2 * p - q := h.1
  have h2 : 0 ≤ 3 * q - 2 * p := h.2.1
  have h3 : 0 ≤ 6 - 2 * q := h.2.2
  have h4 : (sqrt (2 * p - q) + sqrt (3 * q - 2 * p) + sqrt (6 - 2 * q)) ^ 2 ≤ 18 := by
    nlinarith [sq_nonneg (sqrt (2 * p - q) - sqrt (3 * q - 2 * p)), sq_nonneg (sqrt (2 * p - q) - sqrt (6 - 2 * q)), sq_nonneg (sqrt (3 * q - 2 * p) - sqrt (6 - 2 * q)),
      Real.sqrt_nonneg (2 * p - q), Real.sqrt_nonneg (3 * q - 2 * p), Real.sqrt_nonneg (6 - 2 * q),
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 * p - q) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 * q - 2 * p) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (6 - 2 * q) by linarith),
      mul_nonneg (Real.sqrt_nonneg (2 * p - q)) (Real.sqrt_nonneg (3 * q - 2 * p)), mul_nonneg (Real.sqrt_nonneg (2 * p - q)) (Real.sqrt_nonneg (6 - 2 * q)), mul_nonneg (Real.sqrt_nonneg (3 * q - 2 * p)) (Real.sqrt_nonneg (6 - 2 * q)),
      sq_nonneg (sqrt (2 * p - q) * sqrt (3 * q - 2 * p) - 0), sq_nonneg (sqrt (2 * p - q) * sqrt (6 - 2 * q) - 0), sq_nonneg (sqrt (3 * q - 2 * p) * sqrt (6 - 2 * q) - 0)
    ]
  have h6 : (sqrt (2 * p - q) + sqrt (3 * q - 2 * p) + sqrt (6 - 2 * q)) ≤ Real.sqrt 18 := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have h7 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
  nlinarith [Real.sqrt_nonneg (2 * p - q), Real.sqrt_nonneg (3 * q - 2 * p), Real.sqrt_nonneg (6 - 2 * q), Real.sqrt_nonneg 2, Real.sqrt_nonneg 18, h7]