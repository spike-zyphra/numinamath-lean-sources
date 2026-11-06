import Mathlib

theorem number_theory_605252 {n : ℕ} (hn : n > 1) (h : ∑ i ∈ Finset.range n, (i + 1) = 2009) :
    n = 7 → IsGreatest {x | ∃ i, x = ∑ j ∈ Finset.range n, if j ≠ i then (j + 1) else 0} 1994 := by 
  intro h1
  have h4 : ∑ i in Finset.range n, (i + 1) = 28 := by
    rw [h1]
    norm_num [Finset.sum_range_succ]
  have h5 : 28 = 2009 := by
    linarith [h, h4]
  all_goals
    omega