import Mathlib

def s : ℕ → ℕ
| n => (Nat.digits 2 n).sum

theorem number_theory_155355 : (∑ n in Finset.range 16, 2^n * (-1 : ℝ) ^ s n) / 255 = 45 := by 
  norm_num [Finset.sum_range_succ, s]