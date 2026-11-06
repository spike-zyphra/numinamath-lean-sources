import Mathlib

theorem number_theory_5396 : (2 ^ (11 : ℕ) * 3 ^ (22 : ℕ) + 4 ^ (11 : ℕ) * 5 ^ (22 : ℕ) +
    6 ^ (11 : ℕ) * 7 ^ (22 : ℕ) + 8 ^ (11 : ℕ) * 9 ^ (22 : ℕ)) % 10 = 8 := by
  norm_num