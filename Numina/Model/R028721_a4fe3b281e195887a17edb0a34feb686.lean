import Mathlib

theorem algebra_13433 : 90 * r - 44 * r = 46 * r := by
  have eq1 : 90 * r - 44 * r = 46 * r := by
    cases r with
    | zero =>
      simp
    | succ r =>
      simp [Nat.mul_add, Nat.add_sub_cancel] at *
      all_goals omega
  exact eq1