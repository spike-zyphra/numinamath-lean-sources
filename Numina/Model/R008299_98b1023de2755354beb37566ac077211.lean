import Mathlib

theorem number_theory_15910 {n : ℕ} (hn : n ≠ 0) (h : n ≤ 100)
    (h' : 136 * n ≡ 184 [ZMOD 203]) : n = 73 := by
  norm_num [Int.ModEq] at h'
  omega