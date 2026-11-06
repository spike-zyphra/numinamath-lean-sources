import Mathlib

-- The number of positive divisors of ${{2017}^{2017}}$ is ___          ___ .
theorem number_theory_632247 : (Nat.divisors (2017^2017)).card = 2018 := by
  have h1 : Nat.Prime 2017 := by
    norm_num
  rw [Nat.divisors_prime_pow]
  all_goals
    all_goals norm_num
    all_goals norm_num
    all_goals tauto