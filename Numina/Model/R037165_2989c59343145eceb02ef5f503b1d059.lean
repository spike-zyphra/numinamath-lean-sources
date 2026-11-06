import Mathlib

open Nat

theorem number_theory_218361 :
    ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
      a.gcd b > 1 ∧ a.gcd c > 1 ∧ a.gcd d > 1 ∧
      b.gcd c > 1 ∧ b.gcd d > 1 ∧ c.gcd d > 1 ∧
      (a.gcd b).gcd c = 1 ∧ (a.gcd b).gcd d = 1 ∧
      (c.gcd d).gcd a = 1 ∧ (c.gcd d).gcd b = 1 := by
  use 66, 105, 182, 715
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num [Nat.gcd]
  constructor
  · norm_num [Nat.gcd]
  constructor
  · norm_num [Nat.gcd]
  constructor
  · norm_num [Nat.gcd]
  constructor
  · norm_num [Nat.gcd]
  constructor
  · norm_num [Nat.gcd]
  constructor
  · norm_num [Nat.gcd]
  constructor
  · norm_num [Nat.gcd]
  constructor
  · norm_num [Nat.gcd]
  · norm_num [Nat.gcd]