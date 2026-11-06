import Mathlib

theorem algebra_6990 (n : ℕ) (hn : n > 0) (a : ℕ → ℕ)
    (ha : ∀ k, a k = k ^ 3) (h : ∑ i ∈ Finset.Icc 1 n, a i = 1296) :
    n = 8 := by
  have h1 : ∀ i, a i = i ^ 3 := ha
  have eq1 : ∀ k, ∑ i ∈ Finset.Icc 1 k, a i =   ∑ i ∈ Finset.Icc 1 k, (i ^ 3) := by 
    intro k 
    apply Finset.sum_congr 
    · rfl 
    · intro i hi 
      specialize h1 i 
      simpa using h1
  have eq2 : ∑ i ∈ Finset.Icc 1 n, a i = ∑ i ∈ Finset.Icc 1 n, (i ^ 3) := eq1 n
  rw [eq2] at h
  have h2 : n ≤ 20 := by 
    by_contra h3
    push_neg at h3 
    have h3' : ∑ i in Finset.Icc 1 n, (i ^ 3) > 1296 := by 
      have h4 : n ≥ 20 := by linarith 
      have h5 : ∑ i in Finset.Icc 1 n, (i ^ 3) ≥ ∑ i in Finset.Icc 1 20, (i ^ 3) := by 
        apply Finset.sum_le_sum_of_subset_of_nonneg 
        · -- Show that Icc 1 20 ⊆ Icc 1 n 
          intro i hi 
          simp at hi ⊢ 
          omega 
        · -- Show that for i ∈ Icc 1 20, (i: ℕ) ^ 3 ≤ (i: ℕ) ^ 3 
          intro i hi 
          simp 
      have h6 : ∑ i in Finset.Icc 1 20, (i ^ 3) > 1296 := by 
        norm_num [Finset.sum_Icc_succ_top] 
      linarith 
    linarith 
  interval_cases n <;> try { 
    norm_num [Finset.sum_Icc_succ_top] at h <;> try { 
      omega 
    } 
  }