import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_8297 (x : ℝ) (hx : 3 * x - 6 ≥ 0 ∧ 9 - x ≥ 0 ∧ 26 - 2 * x ≥ 0) :
    sqrt (3 * x - 6) + sqrt (9 - x) + sqrt (26 - 2 * x) ≤ 9 := by
  rcases hx with ⟨hx1, hx2, hx3⟩
  have h1 : 2 ≤ x := by linarith
  have h2 : x ≤ 9 := by linarith
  nlinarith [sq_nonneg (sqrt (3 * x - 6) - 3), sq_nonneg (sqrt (9 - x) - 2), sq_nonneg (sqrt (26 - 2 * x) - 4),
          Real.sqrt_nonneg (3 * x - 6), Real.sqrt_nonneg (9 - x), Real.sqrt_nonneg (26 - 2 * x),
          Real.sq_sqrt (show 3 * x - 6 ≥ 0 by linarith),
          Real.sq_sqrt (show 9 - x ≥ 0 by linarith),
          Real.sq_sqrt (show 26 - 2 * x ≥ 0 by linarith),
          mul_self_nonneg (sqrt (3 * x - 6) - 3),
          mul_self_nonneg (sqrt (9 - x) - 2),
          mul_self_nonneg (sqrt (26 - 2 * x) - 4)
          ]