import Mathlib

theorem algebra_51995 {n m : ℕ} (h₀ : n > 0) (h₁ : m ∈ Finset.Icc 1 n)
    (h₂ : ∑ i ∈ Finset.Icc 1 n, i = 1986 - m) :
    m = 33 := by 
  have h3 : m ≥ 1 := by 
    have h4 : m ∈ Finset.Icc 1 n := h₁ 
    simp at h4 
    omega 
  have h5 : m ≤ n := by 
    have h4 : m ∈ Finset.Icc 1 n := h₁ 
    simp at h4 
    omega 
  have h6 : n ≤ 62 := by 
    by_contra h 
    push_neg at h 
    have h7 : n ≥ 63 := by omega 
    have h8 : ∑ i in Finset.Icc 1 n, i ≥ 2016 := by 
      have h9 : n ≥ 63 := h7 
      calc 
        ∑ i in Finset.Icc 1 n, i ≥ ∑ i in Finset.Icc 1 63, i := by 
          apply Finset.sum_le_sum_of_subset_of_nonneg 
          · intro x hx 
            simp at hx ⊢ 
            omega 
          · intro x hx 
            simp at hx ⊢ 
            all_goals omega 
        _ = 2016 := by 
          norm_num [Finset.sum_Icc_succ_top] 
    omega 
  interval_cases n <;> try { 
    norm_num [Finset.sum_Icc_succ_top] at h₂ 
    <;> omega 
  }
  <;> omega