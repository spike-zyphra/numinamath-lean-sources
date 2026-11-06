import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_603075 {a : ℕ → ℝ}
  (ha : ∀ n, a (2 * n - 1) + a (2 * n) = 2 ^ n + 3 * n ∧
    a (2 * n - 1) * a (2 * n) = 3 * n * 2 ^ n)
  (hinc : ∀ n, a (2 * n - 1) ≤ a (2 * n)) :
  ∀ n, 1 / 6 ≤ ∑ i ∈ Finset.range n, (-1) ^ (1 / 2 * (|sin (i + 1)| / sin (i + 1) + 3)) /
    (a (2 * i - 1) * a (2 * i)) ∧
  ∑ i ∈ Finset.range n, (-1) ^ (1 / 2 * (|sin (i + 1)| / sin (i + 1) + 3)) /
    (a (2 * i - 1) * a (2 * i)) ≤ 5 / 24 := by
  intro n
  exfalso
  have h1 := ha 0
  norm_num at h1 ⊢
  all_goals nlinarith [h1.1, h1.2, sq_nonneg (a 0 - 1/2), sq_nonneg (a 0), hinc 0]