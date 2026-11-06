import Mathlib

def f (n : ℕ) : ℕ := (Nat.digits 10 (3 * n ^ 2 + n + 1)).sum

theorem number_theory_9267 : ∃ n, 0 < n ∧ f n = 2012 := by 
  use 2 * 10 ^ 224 - 1
  constructor 
  · -- Show that 2 * 10 ^ 224 - 1 > 0
    norm_num
  · -- Show that f (2 * 10 ^ 224 - 1) = 2012
    native_decide