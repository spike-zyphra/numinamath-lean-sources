import Mathlib

open Real

theorem inequalities_45112 : ∃ n : ℕ, 0 < n ∧ ∀ x ≥ 0, (x - 1) * (x ^ 2005 - 2005 * x ^ (n + 1) + 2005 * x ^ n - 1) ≥ 0 := by 
  use 1002
  constructor
  · norm_num
  · intro x hx
    nlinarith [sq_nonneg (x ^ 1002 - 1), sq_nonneg (x - 1), sq_nonneg (x ^ 1002 - x), sq_nonneg (x ^ 2005 - 1),
        sq_nonneg (x - 1), sq_nonneg (x ^ 501 - 1), sq_nonneg (x ^ 1002 - x ^ 1001), 
        sq_nonneg (x ^ 1002 - 1), sq_nonneg (x ^ 1003 - 1), sq_nonneg (x ^ 1002 - x * 1),
        sq_nonneg (x * (x - 1)), sq_nonneg ((x - 1) * (x ^ 1002 - 1)), mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ x by linarith)]