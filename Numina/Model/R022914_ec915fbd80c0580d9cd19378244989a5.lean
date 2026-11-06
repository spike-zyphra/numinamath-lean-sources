import Mathlib

theorem number_theory_274881 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length = 2893 ↔ n = 1000 := by
  constructor
  · -- Forward direction: if the sum equals 2893, then n = 1000
    intro h
    have h1 : n ≤ 1000 := by
      by_contra h2
      push_neg at h2
      have h3 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length ≥ ∑ i in Finset.Icc 1 1001, (Nat.digits 10 i).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show that Finset.Icc 1 1001 ⊆ Finset.Icc 1 n
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that 0 ≤ (Nat.digits 10 i).length for all i in Finset.Icc 1 1001
          intro i hi
          simp at hi ⊢
          all_goals omega
      have h4 : ∑ i in Finset.Icc 1 1001, (Nat.digits 10 i).length > 2893 := by
        native_decide
      linarith [h, h3, h4]
    have h2 : n ≥ 1000 := by
      by_contra h2
      push_neg at h2
      have h3 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length ≤ ∑ i in Finset.Icc 1 999, (Nat.digits 10 i).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show that Finset.Icc 1 n ⊆ Finset.Icc 1 999
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that 0 ≤ (Nat.digits 10 i).length for all i in Finset.Icc 1 n
          intro i hi
          simp at hi ⊢
          all_goals omega
      have h4 : ∑ i in Finset.Icc 1 999, (Nat.digits 10 i).length < 2893 := by
        native_decide
      linarith [h, h3, h4]
    have h5 : n = 1000 := by
      omega
    assumption
  · -- Backward direction: if n = 1000, then the sum equals 2893
    intro h
    rw [h]
    native_decide