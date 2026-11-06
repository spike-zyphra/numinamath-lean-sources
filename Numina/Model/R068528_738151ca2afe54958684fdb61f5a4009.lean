import Mathlib

theorem algebra_233905 (t : ℕ → ℝ) (ht : ∀ n, t n = t 0 + 1.5 * n) (h : ∑ i in Finset.range 5, t i = 17.5 * 5) :
    t 0 = 14.5 := by
  norm_num [Finset.sum_range_succ, ht 1, ht 2, ht 3, ht 4] at h 
  ring_nf at h 
  linarith