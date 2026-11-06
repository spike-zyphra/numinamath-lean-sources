import Mathlib

theorem number_theory_29872 : (Nat.floor ((5^2017015 : ℝ) / (5^2015 + 7)) % 1000 = 0) := by

  have h1 : Nat.floor ((5^2017015 : ℝ) / (5^2015 + 7)) = (5^2017015 : ℕ) / (5^2015 + 7 : ℕ) := by
    norm_num [Nat.floor_eq_iff]

  rw [h1]

  norm_num