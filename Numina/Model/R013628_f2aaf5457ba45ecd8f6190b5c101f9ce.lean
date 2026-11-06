import Mathlib

/- The page numbers of a book are numbered from $1$ to $n$. When all these page numbers are added together, one of the page numbers was mistakenly added twice, resulting in an incorrect sum of $2019$. $n=$ ___          ___ , and the page number that was added twice is ___          ___. -/
theorem number_theory_4193 (n : ℕ) (h : n > 0) (a : ℕ) (ha : a ∈ Finset.Icc 1 n)
    (h' : ∑ i ∈ Finset.Icc 1 n, i = 2019 - a) :
    n = 63 ∧ a = 3 := by
  rw [Finset.mem_Icc] at ha
  rcases ha with ⟨ha1, han⟩
  have h1 : n ≤ 63 := by
    by_contra h2
    push_neg at h2
    have h2 : n ≥ 64 := by
      omega
    have h3 : ∑ i in Finset.Icc 1 n, i ≥ ∑ i in Finset.Icc 1 64, i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Icc 1 64 ⊆ Icc 1 n
        intro i hi
        simp at hi ⊢
        omega
      · -- Show that ∀ i ∈ Icc 1 64, (fun i => i) i ≤ (fun i => i) i
        intro i hi
        simp
    have h4 : ∑ i in Finset.Icc 1 64, i = 2080 := by
      norm_num [Finset.sum_Icc_succ_top]
    have h5 : ∑ i in Finset.Icc 1 n, i ≥ 2080 := by
      linarith [h3, h4]
    omega
  have h2 : n ≥ 63 := by
    by_contra h2
    push_neg at h2
    have h2 : n ≤ 62 := by
      omega
    have h3 : ∑ i in Finset.Icc 1 n, i ≤ ∑ i in Finset.Icc 1 62, i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- Show that Icc 1 62 ⊇ Icc 1 n when n ≤ 62
        intro i hi
        simp at hi ⊢
        omega
      · -- Show that ∀ i ∈ Icc 1 62, (fun i => i) i ≤ (fun i => i) i
        intro i hi
        simp
    have h4 : ∑ i in Finset.Icc 1 62, i = 1953 := by
      norm_num [Finset.sum_Icc_succ_top]
    have h5 : ∑ i in Finset.Icc 1 n, i ≤ 1953 := by
      linarith [h3, h4]
    omega
  have h3 : n = 63 := by
    omega
  have h4 : ∑ i in Finset.Icc 1 n, i = 2016 := by
    rw [h3]
    norm_num [Finset.sum_Icc_succ_top]
  have h5 : a = 3 := by
    omega
  simp [h3, h5]