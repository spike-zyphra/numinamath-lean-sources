import Mathlib

theorem number_theory_159958 (n : ℕ) (h : n > 0) (x : ℕ) (hx : x ∈ Finset.Icc 1 n)
    (h' : ∑ i ∈ Finset.Icc 1 n, i = 1986 - x) :
    x = 33 := by
  have hx1 : 1 ≤ x := by
    simp at hx
    omega
  have hx2 : x ≤ n := by
    simp at hx
    omega
  have h1 : ∑ i in Finset.Icc 1 n, (i : ℕ) ≤ 1986 := by
    omega
  have h3 : n ≤ 62 := by
    by_contra h4
    push_neg at h4
    have h5 : n ≥ 63 := by omega
    have h6 : ∑ i in Finset.Icc 1 n, i ≥ ∑ i in Finset.Icc 1 63, i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp at hi ⊢
        omega
      · intro i hi
        simp
        all_goals try { linarith }
    have h7 : ∑ i in Finset.Icc 1 63, i = 2016 := by
      norm_num [Finset.sum_Icc_succ_top]
    have h8 : ∑ i in Finset.Icc 1 n, i ≥ 2016 := by linarith [h6, h7]
    have h9 : ∑ i in Finset.Icc 1 n, i ≤ 1986 := by
      omega
    omega
  interval_cases n <;> try { 
    norm_num [Finset.sum_Icc_succ_top] at h' ⊢
    omega
    <;> try { simp_all }
    <;> try { ring_nf at h' ⊢ }
    <;> try { omega }
  }
  all_goals try { simp_all }
  all_goals try { linarith }
  all_goals try { omega }