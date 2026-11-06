import Mathlib

theorem number_theory_287957 (n : ℕ) (h₀ : n > 0) (h₁ : ∑ i ∈ Finset.range n, (Nat.digits 10 (2 * i + 1)).length = 125) :
    n = 60 := by
  have h2 : n ≤ 60 := by
    by_contra h
    push_neg at h
    have h3 : ∑ i in Finset.range n, (Nat.digits 10 (2 * i + 1)).length > 125 := by
      have h4 : n ≥ 61 := by omega
      have h5 : ∑ i in Finset.range n, (Nat.digits 10 (2 * i + 1)).length ≥ ∑ i in Finset.range 61, (Nat.digits 10 (2 * i + 1)).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show that range 61 is a subset of range n
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that each term is non-decreasing
          intro i hi
          simp
      have h6 : ∑ i in Finset.range 61, (Nat.digits 10 (2 * i + 1)).length > 125 := by
        native_decide
      linarith
    linarith
  have h3 : n ≥ 60 := by
    by_contra h
    push_neg at h
    have h4 : n ≤ 59 := by omega
    have h5 : ∑ i in Finset.range n, (Nat.digits 10 (2 * i + 1)).length < 125 := by
      have h5 : ∑ i in Finset.range n, (Nat.digits 10 (2 * i + 1)).length ≤ ∑ i in Finset.range 59, (Nat.digits 10 (2 * i + 1)).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show that range n is a subset of range 59
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that each term is non-decreasing
          intro i hi
          simp
      have h6 : ∑ i in Finset.range 59, (Nat.digits 10 (2 * i + 1)).length < 125 := by
        native_decide
      linarith
    linarith
  have h4 : n ≤ 60 := h2
  have h5 : n ≥ 60 := h3
  linarith