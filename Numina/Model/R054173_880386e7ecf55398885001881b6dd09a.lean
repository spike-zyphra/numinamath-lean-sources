import Mathlib

theorem number_theory_22741 {N : ℕ} (hN : N = ∑ i ∈ Finset.range 30, 10^i * (if i < 13 then 7 else 3)) :
    N % 36 = 25 := by 
  rw [hN]
  norm_num [Finset.sum_range_succ]