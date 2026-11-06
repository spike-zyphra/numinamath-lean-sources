import Mathlib

/- (1453, 3019) -/
abbrev number_theory_4962_solution : (ℕ × ℕ) := (1453, 3019)

theorem number_theory_4962 :
    number_theory_4962_solution.1 < number_theory_4962_solution.2 ∧
    Nat.Prime number_theory_4962_solution.1 ∧
    Nat.Prime number_theory_4962_solution.2 ∧
    number_theory_4962_solution.1 * number_theory_4962_solution.2 = 4386607 ∧
    Nat.totient (number_theory_4962_solution.1 * number_theory_4962_solution.2) = 4382136 := by
  constructor
  · -- Show 1453 < 3019
    norm_num [number_theory_4962_solution]
  constructor
  · -- Show 1453 is prime
    norm_num [number_theory_4962_solution]
  constructor
  · -- Show 3019 is prime
    norm_num [number_theory_4962_solution]
  constructor
  · -- Show 1453 * 3019 = 4386607
    norm_num [number_theory_4962_solution]
  · -- Show totient (1453 * 3019) = 4382136
    native_decide