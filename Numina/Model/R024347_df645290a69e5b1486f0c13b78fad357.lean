import Mathlib

theorem number_theory_217893 (n : ℕ) (h : n > 0) :
    (∑ i ∈ Finset.Icc 1 n, (Nat.digits 10 i).length) ≠ 100 := by
  by_contra h1
  -- We already have a contradiction
  have h3 : n ≤ 55 := by
    by_contra h4
    push_neg at h4
    have h4 : n > 55 := by linarith
    have h5 : (∑ i in Finset.Icc 1 n, (Nat.digits 10 i).length) ≥ (∑ i in Finset.Icc 1 56, (Nat.digits 10 i).length) := by
      have h6 : Finset.Icc 1 56 ⊆ Finset.Icc 1 n := by
        intro i hi
        simp at hi ⊢
        omega
      apply Finset.sum_le_sum_of_subset_of_nonneg h6
      intro i hi
      simp
    have h6 : (∑ i in Finset.Icc 1 56, (Nat.digits 10 i).length) > 100 := by 
      native_decide
    linarith
  interval_cases n <;> try { 
    norm_num [Finset.sum_Icc_succ_top] at h1 
    <;> try { contradiction } 
  }