import Mathlib

theorem number_theory_93995 (n : ℕ) (h : n > 0) :
    ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length * 2 = 13794 ↔ n = 2001 := by
  constructor
  · -- Forward direction
    intro h_eq
    have h1 : n ≤ 2001 := by
      by_contra h2
      push_neg at h2
      have h3 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length * 2 ≥ 
          ∑ i in Finset.Icc 1 2002, (Nat.digits 10 i).length * 2 := by
        have h4 : Finset.Icc 1 2002 ⊆ Finset.Icc 1 n := by
          intro i hi
          simp at hi ⊢
          omega
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact h4
        · intro i hi
          simp
      have h5 : ∑ i in Finset.Icc 1 2002, (Nat.digits 10 i).length * 2 > 13794 := by 
        native_decide
      have h6 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length * 2 > 13794 := by 
        linarith
      linarith [h_eq, h6]
    have h2 : n ≥ 2001 := by
      by_contra h3
      push_neg at h3
      have h4 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length * 2 ≤ 
          ∑ i in Finset.Icc 1 2000, (Nat.digits 10 i).length * 2 := by
        have h5 : Finset.Icc 1 n ⊆ Finset.Icc 1 2000 := by
          intro i hi
          simp at hi ⊢
          omega
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact h5
        · intro i hi
          simp
      have h7 : ∑ i in Finset.Icc 1 2000, (Nat.digits 10 i).length * 2 < 13794 := by 
        native_decide
      have h8 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length * 2 < 13794 := by 
        linarith
      linarith [h_eq, h8]
    have h3 : n = 2001 := by 
      omega
    exact h3
  · -- Backward direction
    intro h_eq
    rw [h_eq]
    native_decide