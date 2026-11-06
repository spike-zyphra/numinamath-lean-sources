import Mathlib

theorem algebra_283463 (S : ℕ → ℤ) (hS : ∀ p, S p = ∑ i ∈ Finset.range 40, (p + (2 * p - 1) * i)) :
    ∑ i ∈ Finset.range 10, S (i + 1) = 80200 := by
  simp_rw [hS]
  norm_num [Finset.sum_range_succ]