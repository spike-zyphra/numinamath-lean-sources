import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_248728 :
  IsGreatest {t : ℝ | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ x^3 + y^3 + 3 * x * y = 1 ∧ t = x^2 * y} (4 / 27) := by
  constructor
  · -- Show 4/27 is in the set
    use 2 / 3, 1 / 3
    norm_num
  · -- Show 4/27 is the greatest element in the set
    intro t ht
    rcases ht with ⟨x, y, hx, hy, h_eq, ht⟩
    nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (y - 1 / 3), sq_nonneg (x - 2 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (x^2 - 4 / 9), sq_nonneg (y - 1 / 3), sq_nonneg (x - 2 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (x * y - 2 / 9), sq_nonneg (x + y - 1), sq_nonneg (x^2 - 4 * y), sq_nonneg (y * (y - 1 / 3)), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith)]