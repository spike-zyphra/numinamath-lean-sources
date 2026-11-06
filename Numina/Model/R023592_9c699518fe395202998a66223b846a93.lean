import Mathlib

def c (n : ℕ) := ∑ i ∈ Finset.range n, 10 ^ i

theorem number_theory_129290 {n : ℕ} (hn : n = 8) :
    (c n) ^ 2 = 123456787654321 := by
  rw [hn]
  norm_num [c, Finset.sum_range_succ]