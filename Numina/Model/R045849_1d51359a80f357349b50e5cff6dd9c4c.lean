import Mathlib

theorem number_theory_68988 : 946 ∈ {n : ℕ |  100 ≤ n ∧ n ≤ 1997 ∧ ∃ k : ℤ, (2^n + 2 : ℚ) / n = k} := by

  constructor
  · -- Show that 100 ≤ 946 
    norm_num 
  constructor 
  · -- Show that 946 ≤ 1997
    norm_num 
  · -- Show that there exists an integer k such that (2^946 + 2) / 946 = k 
    use ((2 ^ 946 + 2) / 946 : ℤ)
    all_goals norm_num