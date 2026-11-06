import Mathlib

theorem algebra_185249 (n : ℕ) (h₀ : n > 1) (h₁ : 400 < ∑ i ∈ Finset.range n, (12 + 2 * i)) (h₂ : ∑ i ∈ Finset.range n, (12 + 2 * i) ≤ 440) :
    n = 16 := by

  have h3 : n ≤ 16 := by
    by_contra h
    push_neg at h
    have h4 : n ≥ 17 := by omega
    have h5 : ∑ i ∈ Finset.range n, (12 + 2 * i) > 440 := by
      have h6 : n ≥ 17 := h4
      have h7 : ∑ i ∈ Finset.range 17, (12 + 2 * i) = 476 := by
        norm_num [Finset.sum_range_succ]
      have h8 : ∑ i ∈ Finset.range 17, (12 + 2 * i) ≤ ∑ i ∈ Finset.range n, (12 + 2 * i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp at hx ⊢
          omega
        · intro i hi
          simp [h6]
          all_goals omega
      linarith [h7, h8]
    linarith

  have h4 : n ≥ 16 := by
    by_contra h
    push_neg at h
    have h5 : n ≤ 15 := by omega
    have h6 : ∑ i ∈ Finset.range n, (12 + 2 * i) ≤ 390 := by
      have h7 : n ≤ 15 := h5
      interval_cases n <;> norm_num [Finset.sum_range_succ] at h₁ h₂ ⊢
      all_goals omega
    linarith

  -- Since n ≥ 16 and n ≤ 16, we can conclude that n must be equal to 16
  have hn : n = 16 := by linarith
  exact hn