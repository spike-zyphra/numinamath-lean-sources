import Mathlib

theorem number_theory_113716 (m n : ℤ) (hm : 0 < m) (hn : 0 < n) :
    (m / n : ℝ) % 1 + (n / m : ℝ) % 1 ≠ 1 := by
  norm_num [Int.floor_eq_iff]
  all_goals
    ring_nf
    <;> norm_num
    all_goals
      try { 
        omega
      }