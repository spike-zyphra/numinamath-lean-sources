import Mathlib

theorem number_theory_236017 {n : ℕ} (h : n * 467 = 1925817 - 9 * 100000 - 7 * 10000) :
    n = 2839 := by
  norm_num at h 
  omega