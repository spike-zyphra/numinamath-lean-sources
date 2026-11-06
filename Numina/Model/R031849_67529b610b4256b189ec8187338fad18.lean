import Mathlib

theorem number_theory_282011 (n : ℕ) (h : n > 0) :
    ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length = 390 ↔ n = 166 := by
  constructor
  · -- Forward direction: if sum = 390, then n = 166
    intro h1
    have h2 : n ≤ 166 := by
      by_contra h2
      push_neg at h2
      have h3 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length > 390 := by
        have h4 : n ≥ 167 := by omega
        have h5 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length ≥ ∑ i in Finset.Icc 1 167, (Nat.digits 10 i).length := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · -- Show that Icc 1 167 ⊆ Icc 1 n
            intro i hi
            simp at hi ⊢
            omega
          · -- Show that for i ∈ Icc 1 167, (Nat.digits 10 i).length ≤ (Nat.digits 10 i).length
            intro i hi
            simp
        have h6 : ∑ i in Finset.Icc 1 167, (Nat.digits 10 i).length > 390 := by
          native_decide
        linarith
      linarith
    have h6 : n ≥ 166 := by
      by_contra h6
      push_neg at h6
      have h7 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length < 390 := by
        have h8 : n ≤ 165 := by omega
        have h9 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length ≤ ∑ i in Finset.Icc 1 165, (Nat.digits 10 i).length := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · -- Show that Icc 1 n ⊆ Icc 1 165
            intro i hi
            simp at hi ⊢
            omega
          · -- Show that for i ∈ Icc 1 n, (Nat.digits 10 i).length ≤ (Nat.digits 10 i).length
            intro i hi
            simp
        have h10 : ∑ i in Finset.Icc 1 165, (Nat.digits 10 i).length < 390 := by
          native_decide
        linarith
      linarith
    have hn : n = 166 := by
      linarith
    tauto
  · -- Backward direction: if n = 166, then sum = 390
    intro h2
    rw [h2]
    native_decide