import Mathlib

theorem algebra_97860 (a : ℕ → ℤ) (ha : a 0 = 1) (ha' : a 1 = 3)
    (ha'' : ∀ n, a (n + 2) = a (n + 1) - a n) :
    ∑ i in Finset.range 100, a i = 5 := by
  norm_num [Finset.sum_range_succ, ha, ha', ha'', add_assoc]
  <;> try { omega }