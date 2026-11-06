import Mathlib

theorem number_theory_7949 (n : ℕ) (h : n > 0) :
    ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length = 2010 ↔ n = 706 := by
  constructor
  · -- Forward: if the total digits is 2010, then n = 706
    intro h1
    have h2 : n ≤ 706 := by
      by_contra h2
      push_neg at h2
      have h3 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length ≥ ∑ i in Finset.Icc 1 707, (Nat.digits 10 i).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show Finset.Icc 1 707 ⊆ Finset.Icc 1 n
          intro x hx
          simp at hx ⊢
          omega
        · -- Show ∀ i ∈ Finset.Icc 1 707, (Nat.digits 10 i).length ≤ (Nat.digits 10 i).length
          intro i hi
          simp
      have h4 : ∑ i in Finset.Icc 1 707, (Nat.digits 10 i).length > 2010 := by native_decide
      have h5 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length > 2010 := by
        linarith [h3, h4]
      linarith
    have h3 : n ≥ 706 := by
      by_contra h3
      push_neg at h3
      have h4 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length ≤ ∑ i in Finset.Icc 1 705, (Nat.digits 10 i).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show Finset.Icc 1 n ⊆ Finset.Icc 1 705
          intro x hx
          simp at hx ⊢
          omega
        · -- Show ∀ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length ≤ (Nat.digits 10 i).length
          intro i hi
          simp
      have h5 : ∑ i in Finset.Icc 1 705, (Nat.digits 10 i).length < 2010 := by native_decide
      have h6 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length < 2010 := by
        linarith [h4, h5]
      linarith
    linarith
  · -- Backward: if n = 706, then the total digits is 2010
    intro h2
    rw [h2]
    native_decide