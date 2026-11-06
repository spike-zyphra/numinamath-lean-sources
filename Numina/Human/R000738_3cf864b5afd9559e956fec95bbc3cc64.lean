import Mathlib

/-
The pages of a book are numbered $1_{}^{}$ through $n_{}^{}$. When the page numbers of the book were added, one of the page numbers was mistakenly added twice, resulting in an incorrect sum of $1986_{}^{}$. What was the number of the page that was added twice?
-/

theorem number_theory_14476
  {n a : ℕ}
  (ha : a ≤ n)
  (h' : ∑ i in Finset.range (n + 1), i = 1986 - a)
  : a = 33
:= by
  -- rw [Finset.sum_range_id] at h'
  -- Estimating `√n ≈ 63`, we apply a bounding argument based on summations and the size of `a`
  -- Both directions will be a contradiction argument
  have lower_bound : 62 ≤ n := by
    by_cases neg : 62 ≤ n
    . simpa
    . simp at *
      have neg : n ≤ 61 := by omega
      have : ∑ i ∈ Finset.range (n + 1), i ≤ ∑ i ∈ Finset.range (61 + 1), i := by
        rw [← Finset.sum_range_add_sum_Ico (fun i => i) (by linarith : n + 1 ≤ 61 + 1)]
        simp
      have : 1986 - a ≤ ∑ i ∈ Finset.range (61 + 1), i := by omega
      rw [Finset.sum_range_id] at this
      absurd ha
      push_neg
      calc
        n ≤ 61 := by simpa
        _ < 95 := by norm_num
        _ ≤ a := by omega
  have upper_bound : n ≤ 62 := by
    by_cases neg : n ≤ 62
    . simpa
    . simp at *
      have neg : 63 ≤ n := by omega
      have : ∑ i ∈ Finset.range (63 + 1), i ≤ ∑ i ∈ Finset.range (n + 1), i := by
        rw [← Finset.sum_range_add_sum_Ico (fun i => i) (by linarith : 63 + 1 ≤ n + 1)]
        simp
      have : ∑ i ∈ Finset.range (63 + 1), i ≤ 1986 - a := by omega
      rw [Finset.sum_range_id] at this
      absurd this
      omega
  -- And now we just solve
  rw [(by linarith : n = 62), Finset.sum_range_id] at h'
  omega