import Mathlib

theorem number_theory_107214 {n : ℕ} (hn : n > 1) (h : ∑ i ∈ Finset.range n, (i + 1) = 2009) :
    n = 7 → IsGreatest {x | ∃ i, x = 2009 - (i + 1)} 1994 := by
  intro hn7
  have h1 : n = 7 := hn7
  have h2 : ∑ i in Finset.range n, (i + 1) = 2009 := h
  rw [h1] at h2
  norm_num [Finset.sum_range_succ] at h2
  all_goals
    try { linarith }