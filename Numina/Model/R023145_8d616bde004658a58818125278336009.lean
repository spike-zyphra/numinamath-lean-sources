import Mathlib

theorem algebra_304867 (a : ℝ) (ha : a ≠ 0) :
    ∏ i ∈ Finset.range 100, a^(i + 1) = a^5050 := by
  have h1 : ∀ n : ℕ, ∏ i ∈ Finset.range n, a ^ (i + 1) = a ^ (∑ i in Finset.range n, (i + 1 : ℕ)) := by
    intro n
    rw [← Finset.prod_pow_eq_pow_sum]
  have h2 : ∏ i ∈ Finset.range 100, a ^ (i + 1) = a ^ (∑ i in Finset.range 100, (i + 1 : ℕ)) := h1 100
  rw [h2]
  norm_num [Finset.sum_range_succ]