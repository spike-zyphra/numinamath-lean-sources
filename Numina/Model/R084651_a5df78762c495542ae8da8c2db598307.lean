import Mathlib

theorem number_theory_105562 : ∃ n : ℤ, Prime (n + (n + 1) + (n + 2) + (n + 3)) := by
  use -1
  norm_num [Int.prime_iff_natAbs_prime]