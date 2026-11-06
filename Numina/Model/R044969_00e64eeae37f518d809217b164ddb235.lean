import Mathlib

theorem number_theory_168004 (n : ℕ) (h₀ : n > 0) (h₁ : ∑ i ∈ Finset.range n, (Nat.digits 10 (i + 1)).length = 1260) :
    n = 456 := by
  have h2 : n ≤ 456 := by
    by_contra h
    push_neg at h
    have h3 : ∑ i in Finset.range n, (Nat.digits 10 (i + 1)).length > 1260 := by
      have h4 : n ≥ 457 := by omega
      have h5 : ∑ i in Finset.range n, (Nat.digits 10 (i + 1)).length ≥ ∑ i in Finset.range 457, (Nat.digits 10 (i + 1)).length := by 
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show that {0, 1, ..., 456} is a subset of {0, 1, ..., n-1}
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that ∀ i ∈ {0, 1, ..., 456}, (Nat.digits 10 (i + 1)).length ≤ (Nat.digits 10 (i + 1)).length
          intro i hi
          simp at hi ⊢
          all_goals omega
      have h5' : ∑ i in Finset.range 457, (Nat.digits 10 (i + 1)).length > 1260 := by 
        native_decide
      linarith
    linarith
  have h6 : n ≥ 456 := by
    by_contra h
    push_neg at h
    have h7 : ∑ i in Finset.range n, (Nat.digits 10 (i + 1)).length < 1260 := by 
      have h8 : n ≤ 455 := by omega
      interval_cases n <;> native_decide
    linarith
  have hn : n = 456 := by 
    omega
  exact hn