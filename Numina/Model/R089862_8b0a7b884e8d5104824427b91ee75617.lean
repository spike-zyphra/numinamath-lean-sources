import Mathlib

theorem number_theory_125089 {n : ℕ} (hn : n > 0) (h : 2 * n = 2 + 1 / 4) :
    n ≤ 8 := by
  norm_num at h 
  omega