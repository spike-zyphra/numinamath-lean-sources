import Mathlib

theorem number_theory_2918 :
    Nat.gcd 2022 3707 * Nat.lcm 2022 3707 = 7495554 := by
  norm_num [Nat.gcd, Nat.lcm]