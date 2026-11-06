import Mathlib

theorem number_theory_216312 (n : ℕ) (h₀ : n > 0) (h₁ : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length = 1101) :
    n = 403 := by
  have h2 : n ≤ 403 := by
    by_contra h
    push_neg at h
    have h3 : n ≥ 404 := by omega
    have h4 : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length ≥ ∑ i ∈ Finset.Icc 1 404, (Nat.digits 10 i).length := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Icc 1 404 is a subset of Icc 1 n
        intro x hx
        simp at hx ⊢
        omega
      · -- Show that each term is non-negative
        intro x hx
        simp
    have h5 : ∑ i ∈ Finset.Icc 1 404, (Nat.digits 10 i).length ≥ 1104 := by
      native_decide
    have h6 : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length ≥ 1104 := by
      linarith
    linarith
  have h3 : n ≥ 403 := by
    by_contra h
    push_neg at h
    have h4 : n ≤ 402 := by omega
    have h5 : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length ≤ ∑ i ∈ Finset.Icc 1 402, (Nat.digits 10 i).length := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Icc 1 n is a subset of Icc 1 402
        intro x hx
        simp at hx ⊢
        omega
      · -- Show that each term is non-negative
        intro x hx
        simp
    have h6 : ∑ i ∈ Finset.Icc 1 402, (Nat.digits 10 i).length ≤ 1098 := by
      native_decide
    have h7 : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length ≤ 1098 := by
      linarith
    linarith
  linarith