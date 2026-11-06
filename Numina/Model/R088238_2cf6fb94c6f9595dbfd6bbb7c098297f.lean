import Mathlib

def f (n : ℕ) := n * (n - 1) / 2 + 1

theorem number_theory_279723 :
    ∃ n, ∃ m, f n = 2016 + m := by
  use 64
  use 1
  norm_num [f]