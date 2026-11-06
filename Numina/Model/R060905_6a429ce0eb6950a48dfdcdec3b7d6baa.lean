import Mathlib

theorem number_theory_318361 (n : ℕ) (h₀ : n > 0) (h₁ : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length = 636) :
    n = 248 := by
  have h2 : n ≤ 248 := by
    by_contra h
    push_neg at h
    have h3 : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length ≥ ∑ i ∈ Finset.Icc 1 249, (Nat.digits 10 i).length := by
      have h4 : Finset.Icc 1 249 ⊆ Finset.Icc 1 n := by
        intro x hx
        simp at hx ⊢
        all_goals omega
      apply Finset.sum_le_sum_of_subset_of_nonneg h4
      intro x hx
      simp
    have h4 : ∑ i ∈ Finset.Icc 1 249, (Nat.digits 10 i).length > 636 := by
      native_decide
    linarith
  have h3 : n ≥ 248 := by
    by_contra h
    push_neg at h
    have h4 : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length < 636 := by
      have h5 : n ≤ 247 := by omega
      have h6 : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length ≤ ∑ i ∈ Finset.Icc 1 247, (Nat.digits 10 i).length := by
        have h7 : Finset.Icc 1 n ⊆ Finset.Icc 1 247 := by
          intro x hx
          simp at hx ⊢
          omega
        apply Finset.sum_le_sum_of_subset_of_nonneg h7
        intro x hx
        simp
      have h7 : ∑ i ∈ Finset.Icc 1 247, (Nat.digits 10 i).length < 636 := by
        native_decide
      linarith
    linarith [h₁, h4]
  linarith