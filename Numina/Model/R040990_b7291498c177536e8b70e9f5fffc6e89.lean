import Mathlib

theorem number_theory_110319 (m : ℕ) (hm : m > 1) (n : ℕ) (h : ∑ i ∈ Finset.range m, (n + i) = 33) :
    m = 2 ∨ m = 3 ∨ m = 6 := by

  have h1 : m ≤ 33 := by
    have h1 : ∑ i in Finset.range m, (n + i) ≥ m * n := by
      have h2 : ∀ i : ℕ, i ∈ Finset.range m → n + i ≥ n := by
        intro i hi
        simp at hi ⊢
        all_goals omega
      have h3 : ∑ i in Finset.range m, (n + i) ≥ ∑ i in Finset.range m, n := by
        apply Finset.sum_le_sum 
        intro i hi
        specialize h2 i hi
        linarith 
      have h4 : ∑ i in Finset.range m, n = m * n := by
        simp [Finset.sum_const, Finset.card_range, mul_comm]
      linarith [h3, h4]
    have h2 : m * n ≤ 33 := by linarith [h, h1]
    by_contra h4
    push_neg at h4 
    have h3 : m > 33 := by linarith
    have h4 : m * n ≥ 34 := by 
      by_contra h5 
      push_neg at h5 
      have h0 : n = 0 := by 
        nlinarith [show m > 0 from by linarith]
      -- Now, n = 0 and m > 33 (m ≥ 34)
      have h51 : ∑ i in Finset.range m, (n + i) = ∑ i in Finset.range m, (i : ℕ) := by
        apply Finset.sum_congr 
        · -- Show the two summation indices are the same
          rfl 
        · -- Show that for each i in the sum, the terms with n=0 are the same
          intro i hi 
          simp [h0] 
      have h52 : ∑ i in Finset.range m, (i : ℕ) ≥ 561 := by 
        have h53 : ∑ i in Finset.range m, (i : ℕ) ≥ ∑ i in Finset.range 34, (i : ℕ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg 
          · -- Show that `Finset.range 34` is a subset of `Finset.range m` if `m ≥ 34`
            intro i hi 
            simp at hi ⊢ 
            omega 
          · -- Show that for i in `Finset.range 34`, `i ≤ i`
            intro i hi 
            all_goals simp 
        have h54 : ∑ i in Finset.range 34, (i : ℕ) = 561 := by 
          norm_num [Finset.sum_range_succ]
        linarith [h53, h54]
      have h53 : ∑ i in Finset.range m, (n + i) = 33 := h
      rw [h51] at h53
      omega 
    nlinarith 
  have h1 : m ≤ 33 := h1 
  interval_cases m <;> try { 
    norm_num [Finset.sum_range_succ] at h ⊢ 
    all_goals 
      omega 
  }
  <;> try { 
    all_goals 
      tauto 
  }