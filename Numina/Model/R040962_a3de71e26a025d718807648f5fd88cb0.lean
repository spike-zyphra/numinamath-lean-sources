import Mathlib

theorem number_theory_290015 {n m : ℕ} (hn : n = ∑ i ∈ Finset.range 25, 10^i * 3)
    (hm : m = ∑ i ∈ Finset.range 25, 10^i * 6) :
    (n * m) = (∑ i ∈ Finset.range 24, 10^(i+26) * 2) + 10^25 * 1 + 
              (∑ i ∈ Finset.range 24, 10^(i+1) * 7) + 8 := by 
  rw [hn, hm]
  norm_num [Finset.sum_range_succ]