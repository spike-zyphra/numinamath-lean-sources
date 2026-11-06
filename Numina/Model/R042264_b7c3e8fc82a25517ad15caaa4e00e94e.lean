import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_214975 (a b c : ℝ) (h : a + b + c = 1) (ha : 3 * a + 1 ≥ 0)(hb : 3 * b + 1 ≥ 0) (hc : 3 * c + 1 ≥ 0) :
    sqrt (3 * a + 1) + sqrt (3 * b + 1) + sqrt (3 * c + 1) ≤ 3 * sqrt 2 := by
  have h1 : (sqrt (3 * a + 1) + sqrt (3 * b + 1) + sqrt (3 * c + 1)) ^ 2 ≤ 18 := by
    nlinarith [sq_nonneg (sqrt (3 * a + 1) - sqrt (3 * b + 1)), 
      sq_nonneg (sqrt (3 * a + 1) - sqrt (3 * c + 1)), 
      sq_nonneg (sqrt (3 * b + 1) - sqrt (3 * c + 1)),
      Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc,
      mul_nonneg (Real.sqrt_nonneg (3 * a + 1)) (Real.sqrt_nonneg (3 * b + 1)),
      mul_nonneg (Real.sqrt_nonneg (3 * a + 1)) (Real.sqrt_nonneg (3 * c + 1)),
      mul_nonneg (Real.sqrt_nonneg (3 * b + 1)) (Real.sqrt_nonneg (3 * c + 1)),
      show (3 * a + 1 + 3 * b + 1 + 3 * c + 1 : ℝ) = 6 by 
        have h' : a + b + c = 1 := h
        linarith
    ]
  have h2 : sqrt (3 * a + 1) + sqrt (3 * b + 1) + sqrt (3 * c + 1) ≤ Real.sqrt 18 := by
    apply Real.le_sqrt_of_sq_le
    linarith [h1]
  have h3 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  linarith [h2, h3, Real.sqrt_nonneg (3 * a + 1), Real.sqrt_nonneg (3 * b + 1), Real.sqrt_nonneg (3 * c + 1), Real.sqrt_nonneg 2]