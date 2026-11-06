import Mathlib

theorem number_theory_119913 (n : ℕ) (h : n > 0) :
    ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length = 777 ↔ n = 295 := by
  constructor
  · -- Assume the sum equals 777, prove n = 295
    intro h1
    have h2 : n ≤ 295 := by
      by_contra h2
      push_neg at h2
      have h3 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length ≥ ∑ i in Finset.Icc 1 296, (Nat.digits 10 i).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show that Finset.Icc 1 296 ⊆ Finset.Icc 1 n
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that for i ∈ Finset.Icc 1 296, the term is ≤ the term in Finset.Icc 1 n
          intro i hi
          simp
      have h4 : ∑ i in Finset.Icc 1 296, (Nat.digits 10 i).length > 777 := by native_decide
      linarith
    have h4 : n ≥ 295 := by
      by_contra h4
      push_neg at h4
      have h5 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length ≤ ∑ i in Finset.Icc 1 294, (Nat.digits 10 i).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show that Finset.Icc 1 n ⊆ Finset.Icc 1 294
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that for i ∈ Finset.Icc 1 n, the term is ≤ the term in Finset.Icc 1 294
          intro i hi
          simp
      have h6 : ∑ i in Finset.Icc 1 294, (Nat.digits 10 i).length < 777 := by native_decide
      linarith
    linarith
  · -- Assume n = 295, prove the sum equals 777
    intro h2
    rw [h2]
    native_decide