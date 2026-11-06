import Mathlib

theorem number_theory_15349 (n : ℕ) (hn : 0 ≤ n ∧ n < 9)
    (h : 1 + 22 + 333 + 4444 + 55555 + 666666 + 7777777 + 88888888 ≡ n [MOD 9]) :
    n = 6 := by
  norm_num [Nat.ModEq] at h 
  omega