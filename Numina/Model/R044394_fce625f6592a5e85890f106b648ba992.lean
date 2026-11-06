import Mathlib

theorem number_theory_209648 :
    ∃ n m, n = 2016 * m ∧ (Nat.digits 10 n).sum = (Nat.digits 10 m).sum * 2016 - 2016 := by 
  use 0, 0
  constructor
  · -- Show that n = 2016 * m
    all_goals norm_num
  · -- Show the digit sum condition
    all_goals 
      native_decide