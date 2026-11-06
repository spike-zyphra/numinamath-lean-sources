import Mathlib

theorem number_theory_278633 (n : ℕ) (h₀ : n > 0) (h₁ : ∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).count 0 = 35) :
    n = 204 := by
  have h2 : n ≤ 204 := by
    by_contra h
    push_neg at h
    have h3 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).count 0 ≥ ∑ i in Finset.Icc 1 205, (Nat.digits 10 i).count 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Finset.Icc 1 n is a subset of Finset.Icc 1 205
        intro i hi
        simp at hi ⊢
        omega
      · -- Show that for i ∈ Finset.Icc 1 n, (Nat.digits 10 i).count 0 ≤ (Nat.digits 10 i).count 0
        intro i hi
        simp
    have h4 : ∑ i in Finset.Icc 1 205, (Nat.digits 10 i).count 0 > 35 := by
      native_decide
    linarith [h₁, h3, h4]

  have h3 : n ≥ 204 := by
    by_contra h
    push_neg at h
    have h4 : ∑ i in Finset.Icc 1 n, (Nat.digits 10 i).count 0 < 35 := by
      interval_cases n <;> native_decide
    omega

  linarith