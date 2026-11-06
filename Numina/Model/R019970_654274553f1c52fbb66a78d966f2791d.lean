import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_325938 {a : ℕ → ℝ}
  (ha : ∀ n, a (2 * n - 1) + a (2 * n) = 2 ^ n + 3 * n ∧ a (2 * n - 1) * a (2 * n) = 3 * n * 2 ^ n)
  (hinc : ∀ n, a (2 * n - 1) ≤ a (2 * n)) :
  ∀ n, 1 / 6 ≤ ∑ i in Finset.Icc 1 n, (-1) ^ (i + 1) / (a (2 * i - 1) * a (2 * i)) ∧
  ∑ i in Finset.Icc 1 n, (-1) ^ (i + 1) / (a (2 * i - 1) * a (2 * i)) ≤ 5 / 24 := by

  have h1 := ha 0
  norm_num at h1 
  all_goals nlinarith [hinc 0]