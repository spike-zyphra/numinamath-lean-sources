import Mathlib

theorem number_theory_167730 (n : ℕ) (hn : n ≤ 100) (h : ∑ i ∈ Finset.Icc 1 n, i = 2021 - ∑ i ∈ Finset.Icc 1 (100 - n), i) :
    n ≤ 43 := by 
  by_contra h1
  push_neg at h1
  have h2 : n > 43 := by omega
  have h3 : n ≤ 100 := by linarith
  have h4 : n ≥ 44 := by omega
  have h5 : n ≤ 100 := by linarith
  interval_cases n <;> try { 
    norm_num [Finset.sum_Icc_succ_top] at h 
    all_goals omega
  }