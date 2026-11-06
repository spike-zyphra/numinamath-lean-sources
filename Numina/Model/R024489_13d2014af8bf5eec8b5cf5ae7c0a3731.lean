import Mathlib

theorem algebra_186456 {a : ℕ → ℝ} (h₀ : ∀ n, a n = a 0 * (1 / 3) ^ n)
    (h₁ : a 3 = 1 / 54) (h₂ : ∑ i in Finset.range n, a i = 121 / 162) :
    n = 5 := by
  have ha3 : a 3 = a 0 * (1 / 3) ^ 3 := h₀ 3
  rw [ha3] at h₁
  have ha0 : a 0 = 1 / 2 := by
    norm_num at h₁
    linarith
  have h3 : ∀ i, a i = (1 / 2) * (1 / 3) ^ i := by
    intro i
    specialize h₀ i
    rw [h₀]
    rw [ha0]
  have h5 : n ≤ 10 := by
    by_contra h
    push_neg at h
    have h8 : ∑ i in Finset.range n, a i > 121 / 162 := by
      have h9 : n ≥ 11 := by omega
      have h11 : ∑ i in Finset.range n, a i ≥ ∑ i in Finset.range 11, a i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show Finset.range 11 ⊆ Finset.range n
          intro i hi
          simp at hi ⊢
          omega
        · -- Show non-negativity of terms
          intro i hi
          simp [h3]
          all_goals norm_num
      have h12 : ∑ i in Finset.range 11, a i > 121 / 162 := by
        norm_num [Finset.sum_range_succ, h3]
      linarith [h11, h12]
    linarith [h₂, h8]
  have h6 : n = 5 := by
    interval_cases n <;> norm_num [Finset.sum_range_succ, h3] at h₂ <;> norm_num at h₂ <;> try linarith
  exact h6