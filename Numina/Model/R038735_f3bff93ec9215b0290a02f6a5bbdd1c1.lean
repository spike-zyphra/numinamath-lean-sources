import Mathlib

theorem number_theory_188018 : ∃ x y, x * y = 1000000000 ∧ ¬∃ i, (Nat.digits 10 x).get i = 0 ∧ ¬∃ i, (Nat.digits 10 y).get i = 0 := by
  use 512, 1953125
  constructor
  . norm_num
  all_goals
    native_decide