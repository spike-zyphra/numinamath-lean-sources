import Mathlib

theorem number_theory_130247 : {(n, k) : ℕ × ℕ | n > 0 ∧ k > 1 ∧ ∑ i ∈ Finset.range k, (n + i) = 2003} =
    {(1001, 2)} := by
  ext ⟨n, k⟩
  simp
  constructor
  · -- First, prove that if \((n, k)\) is in the left set, then \((n, k) = (1001, 2)\).
    rintro ⟨hn, hk, hsum⟩
    have h1 : k ≤ 63 := by
      by_contra h
      push_neg at h
      have h2 : ∑ i in Finset.range k, (n + i) > 2003 := by
        have h3 : k ≥ 64 := by omega
        have h4 : ∑ i in Finset.range k, (n + i) ≥ ∑ i in Finset.range 64, (n + i) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · -- Show `Finset.range 64 ⊆ Finset.range k`.
            intro i hi
            simp at hi ⊢
            omega
          · -- For each `i` in `Finset.range 64`, show `(n + i) ≤ (n + i)`.
            intro i hi
            simp
        have h5 : ∑ i in Finset.range 64, (n + i) > 2003 := by
          norm_num [Finset.sum_range_succ] at *
          all_goals
            omega
        linarith
      linarith
    interval_cases k <;> norm_num [Finset.sum_range_succ] at hsum ⊢
    <;> omega
  · -- Now prove the converse: \((1001, 2)\) is in the left set.
    rintro (⟨rfl, rfl⟩)
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Verify that ∑ i in range 2, (1001 + i) = 2003.
      norm_num [Finset.sum_range_succ]