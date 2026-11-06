import Mathlib

theorem algebra_328424 (P : ℝ × ℝ) (hP : 2 * P.1 ^ 2 - 5 * P.1 * P.2 + 2 * P.2 ^ 2 = 1) :
    Real.sqrt (P.1 ^ 2 + P.2 ^ 2) ≥ Real.sqrt 2 / 3 := by
  have h1 : P.1 ^ 2 + P.2 ^ 2 ≥ 2 / 9 := by
    nlinarith [sq_nonneg (P.1 - P.2), sq_nonneg (P.1 + P.2), sq_nonneg (2 * P.1 - P.2), sq_nonneg (P.1 - 2 * P.2), sq_nonneg (P.1 - 1 / 3), sq_nonneg (P.2 + 1 / 3), sq_nonneg (P.1 + 1 / 3), sq_nonneg (P.2 - 1 / 3)]
  have h2 : Real.sqrt (P.1 ^ 2 + P.2 ^ 2) ≥ Real.sqrt (2 / 9) := by
    apply Real.sqrt_le_sqrt
    linarith [h1]
  have h3 : Real.sqrt (2 / 9) = Real.sqrt 2 / 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h3] at h2
  linarith [h2, Real.sqrt_nonneg (P.1 ^ 2 + P.2 ^ 2), Real.sqrt_nonneg (2)]