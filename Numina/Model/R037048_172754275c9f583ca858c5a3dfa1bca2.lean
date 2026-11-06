import Mathlib
import Mathlib.Tactic

theorem algebra_93770 :
  ∃ (x y z : Int),
    x + y + z = 96
    ∧ x = 6 * z
    ∧ z = y - 40
    ∧ Int.natAbs (x - y) = 5 := by
  use 42, 47, 7
  constructor
  · -- show that 42 + 47 + 7 = 96
    norm_num
  constructor
  · -- show that 42 = 6 * 7
    norm_num
  constructor
  · -- show that 7 = 47 - 40
    norm_num
  · -- show that the absolute value of (42 - 47) is 5
    norm_num [Int.natAbs]