import Mathlib

theorem algebra_187746 (n : ℕ) :
    ∏ i ∈ Finset.range n, 3^(3 * i + 2) = 27^5 ↔ n = 3 := by
  constructor
  · -- Forward: if the product equals 27^5, then n = 3
    intro h
    have h1 : ∀ n : ℕ, ∏ i ∈ Finset.range n, 3^(3 * i + 2) = 3 ^ (∑ i in Finset.range n, (3 * i + 2)) := by
      intro n
      rw [Finset.prod_pow_eq_pow_sum]
    have h2 : ∏ i ∈ Finset.range n, 3^(3 * i + 2) = 3 ^ (∑ i in Finset.range n, (3 * i + 2)) := h1 n
    rw [h2] at h
    have h3 : (27 : ℕ) ^ 5 = 3 ^ 15 := by norm_num
    rw [h3] at h
    -- We now solve for ∑ i in Finset.range n, (3 * i + 2) from ( power equality )
    have h4 : ∑ i in Finset.range n, (3 * i + 2) = 15 := by
      exact Nat.pow_right_injective (by norm_num) h
    have h5 : n ≤ 5 := by
      by_contra h
      push_neg at h
      have h6 : ∑ i in Finset.range n, (3 * i + 2) ≥ ∑ i in Finset.range 6, (3 * i + 2) := by
        have h7 : Finset.range 6 ⊆ Finset.range n := by
          intro i hi
          simp at hi ⊢
          omega
        apply Finset.sum_le_sum_of_subset_of_nonneg h7
        intro i hi
        simp
      have h7 : ∑ i in Finset.range 6, (3 * i + 2) = 57 := by
        norm_num [Finset.sum_range_succ]
      have h8 : ∑ i in Finset.range n, (3 * i + 2) ≥ 57 := by
        linarith [h6, h7]
      omega
    interval_cases n <;> try { 
      norm_num [Finset.sum_range_succ] at h4
      all_goals
      omega
    }
  · -- Backward: if n = 3, then the product equals 27^5
    intro h
    rw [h]
    norm_num [Finset.prod_range_succ, pow_add]