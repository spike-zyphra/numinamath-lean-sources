import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_77596 (x y : ℝ) (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    5 * (x ^ 2 + y ^ 2) ^ 2 ≤ 4 + (x + y) ^ 4 := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1),
          sq_nonneg (x^2 - y^2), sq_nonneg (x * y - x * y), sq_nonneg (x - y), sq_nonneg (x^2 + y^2 -1),
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith),
          mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - y by linarith),
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ 1 - x by linarith),
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ 1 - y by linarith)]