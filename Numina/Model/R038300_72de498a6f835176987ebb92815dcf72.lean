import Mathlib

theorem number_theory_608457{M:ℝ}(hM: M = 5):
  ∃ k:ℕ, ∑ i ∈ Finset.range k, ((1:ℝ)/(1+i)) > M := by 
  use 83
  rw [hM]
  norm_num [Finset.sum_range_succ]