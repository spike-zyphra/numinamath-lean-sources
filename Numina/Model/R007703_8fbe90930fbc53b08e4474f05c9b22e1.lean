import Mathlib

theorem number_theory_4506 :
    Int.gcd 15 35 = 5 ∧
    Int.gcd 0 111 = 111 ∧
    Int.gcd (-12) 18 = 6 ∧
    Int.gcd 99 100 = 1 ∧
    Int.gcd 11 121 = 11 ∧
    Int.gcd 100 102 = 2 := by
  constructor
  · -- Show gcd(15, 35) = 5
    norm_num [Int.gcd]
  constructor
  · -- Show gcd(0, 111) = 111
    norm_num [Int.gcd]
  constructor
  · -- Show gcd(-12, 18) = 6
    norm_num [Int.gcd]
  constructor
  · -- Show gcd(99, 100) = 1
    norm_num [Int.gcd]
  constructor
  · -- Show gcd(11, 121) = 11
    norm_num [Int.gcd]
  · -- Show gcd(100, 102) = 2
    norm_num [Int.gcd]