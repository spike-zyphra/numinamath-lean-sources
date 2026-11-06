import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_39986 :
  IsGreatest {y | ∃ x : ℝ, y = x^3 - 3 * x ∧ x^4 + 36 ≤ 13 * x^2} 18 := by
  constructor
  · -- Show that 18 is in the set
    use 3
    norm_num
  · -- Show that any element in the set is ≤ 18
    intro y hy
    rcases hy with ⟨x, hx1, hx2⟩
    nlinarith [sq_nonneg (x ^ 2 - 9), sq_nonneg (x ^ 2 - 4), sq_nonneg (x - 3), sq_nonneg (x + 3), sq_nonneg (x * (x ^ 2 - 1)), sq_nonneg (x * (x - 3)), sq_nonneg (x * (x + 3)), sq_nonneg ((x) ^ 2 * (x - 3)), sq_nonneg ((x) ^ 2 * (x + 3)), sq_nonneg (x ^ 2 * (x ^ 2 - 1))]