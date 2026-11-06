import Mathlib

def pentagonal (n : ℕ) := n * (3 * n - 1) / 2

theorem number_theory_151727 : pentagonal 10 = 145 := by 
  unfold pentagonal
  norm_num