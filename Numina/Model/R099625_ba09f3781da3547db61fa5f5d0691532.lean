import Mathlib

theorem number_theory_244778 (n : ℕ) (h : n > 0) (a b : ℕ)
    (ha : a = n + 1) (hb : b = n + 16) (h' : ∑ i ∈ Finset.range 17, (a + i) = 344) :
    n = 16 := by 
  rw [ha] at h'
  norm_num [Finset.sum_range_succ] at h'
  omega