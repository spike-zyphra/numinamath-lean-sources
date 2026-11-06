import Mathlib

theorem number_theory_156670 (n : ℕ) (h₀ : n > 0) (h₁ : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).sum = 10000) :
    n = 799 := by
  have h2 : n ≤ 799 := by
    by_contra h
    push_neg at h
    have h3 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).sum ≥ ∑ i in Finset.Icc 1 800, (Nat.digits 10 i).sum := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Finset.Icc 1 800 is a subset of Finset.Icc 1 n
        intro i hi
        simp at hi ⊢
        omega
      · -- Show that for each i in Finset.Icc 1 800, (Nat.digits 10 i).sum ≤ (Nat.digits 10 i).sum
        intro i hi
        simp at hi ⊢
    have h4 : ∑ i in Finset.Icc 1 800, (Nat.digits 10 i).sum > 10000 := by
      native_decide
    have h5 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).sum > 10000 := by
      linarith [h3, h4]
    linarith [h₁, h5]

  have h4 : n ≥ 799 := by
    by_contra h
    push_neg at h
    have h5 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).sum ≤ ∑ i in Finset.Icc 1 798, (Nat.digits 10 i).sum := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Finset.Icc 1 n is a subset of Finset.Icc 1 798
        intro i hi
        simp at hi ⊢
        omega
      · -- Show that for each i in Finset.Icc 1 n, (Nat.digits 10 i).sum ≤ (Nat.digits 10 i).sum
        intro i hi
        simp at hi ⊢
    have h6 : ∑ i in Finset.Icc 1 798, (Nat.digits 10 i).sum < 10000 := by
      native_decide
    have h7 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).sum < 10000 := by
      linarith [h5, h6]
    linarith [h₁, h7]

  have h5 : n = 799 := by
    omega
  exact h5