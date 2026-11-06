import Mathlib

theorem number_theory_222461 (n : ℕ) (h : n > 0) :
    ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length = 2022 ↔ n = 710 := by
  constructor
  · -- Assume that the sum is 2022, prove n = 710
    intro h1
    have h2 : n ≤ 710 := by
      by_contra h3
      push_neg at h3
      have h4 : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length > 2022 := by
        have h5 : n ≥ 711 := by omega
        have h6 : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length ≥
          ∑ i ∈ Finset.Icc 1 711, (Nat.digits 10 i).length := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · -- Show that Finset.Icc 1 711 ⊆ Finset.Icc 1 n when n ≥ 711
            intro i hi
            simp at hi ⊢
            omega
          · -- Show that ∀ i ∈ Finset.Icc 1 711, 0 ≤ (Nat.digits 10 i).length
            intro i hi
            simp at hi ⊢
            all_goals omega
        have h7 : (∑ i ∈ Finset.Icc 1 711, (Nat.digits 10 i).length) > 2022 := by native_decide
        linarith
      linarith
    have h3 : n ≥ 710 := by
      by_contra h4
      push_neg at h4
      have h4 : n ≤ 709 := by omega
      have h5 : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length ≤
        ∑ i ∈ Finset.Icc 1 709, (Nat.digits 10 i).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show that Finset.Icc 1 n ⊆ Finset.Icc 1 709 when n ≤ 709
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that ∀ i ∈ Finset.Icc 1 n, 0 ≤ (Nat.digits 10 i).length
          intro i hi
          simp at hi ⊢
        all_goals omega
      have h6 : (∑ i ∈ Finset.Icc 1 709, (Nat.digits 10 i).length) < 2022 := by native_decide
      linarith
    have h7 : n = 710 := by
      omega
    exact h7
  · -- Assume n = 710, prove the sum = 2022
    intro h2
    rw [h2]
    native_decide