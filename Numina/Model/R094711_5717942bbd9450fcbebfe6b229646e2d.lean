import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_238546 (A B : ℝ × ℝ)
  (hA : A.1 > 0) (hB : B.1 > 0)
  (hA' : A.1^2 - A.2^2 = 1) (hB' : B.1^2 - B.2^2 = 1) :
  (A.1 * B.1 + A.2 * B.2) ≥ 1 := by
    nlinarith [sq_nonneg (A.1 - B.1), sq_nonneg (A.2 - B.2), sq_nonneg (A.1 + B.1), sq_nonneg (A.2 + B.2), 
      mul_pos hA hB, sq_nonneg (A.1 * B.1 - 1), sq_nonneg (A.2 * B.2)]