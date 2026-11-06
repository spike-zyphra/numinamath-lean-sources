import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_129341 {A B : ℝ × ℝ}
  (hA : A.1^2 - A.2^2 = 2) (hB : B.1^2 - B.2^2 = 2)
  (hAB : A.1 > 0) (hBA : B.1 > 0) :
  (A.1 * B.1 + A.2 * B.2) ≥ 2 := by
  nlinarith [sq_nonneg (A.1 - B.1), sq_nonneg (A.2 - B.2),
            sq_nonneg (A.1 * B.2 - A.2 * B.1),
            sq_nonneg (A.1 + B.1), sq_nonneg (A.2 + B.2),
            mul_pos hAB hBA, sq_nonneg (A.1 - B.1), sq_nonneg (A.2 - B.2)]