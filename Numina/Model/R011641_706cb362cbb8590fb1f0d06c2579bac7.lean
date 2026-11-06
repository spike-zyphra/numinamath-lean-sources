import Mathlib

open Nat

theorem number_theory_263587 :
    ∃ a b c : ℕ,
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      Nat.lcm (a * b) c = 2 ^ 8 ∧
      Nat.lcm (b * c) a = 2 ^ 9 ∧
      Nat.lcm (c * a) b = 2 ^ 11 ∧
      (a = 2 ^ 3 ∧ b = 2 ^ 1 ∧ c = 2 ^ 8 ∨
       a = 2 ^ 5 ∧ b = 2 ^ 3 ∧ c = 2 ^ 6) := by
  use 2 ^ 3, 2 ^ 1, 2 ^ 8
  constructor
  · -- Show a ≠ 0
    norm_num
  constructor
  · -- Show b ≠ 0
    norm_num
  constructor
  · -- Show c ≠ 0
    norm_num
  constructor
  · -- Show Nat.lcm (a * b) c = 2 ^ 8
    native_decide
  constructor
  · -- Show Nat.lcm (b * c) a = 2 ^ 9
    native_decide
  constructor
  · -- Show Nat.lcm (c * a) b = 2 ^ 11
    native_decide
  left
  constructor
  · -- Show a = 2 ^ 3
    rfl
  constructor
  · -- Show b = 2 ^ 1
    rfl
  · -- Show c = 2 ^ 8
    rfl