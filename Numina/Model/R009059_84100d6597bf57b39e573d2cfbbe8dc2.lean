import Mathlib
import Mathlib.Tactic.NormNum

theorem number_theory_93248 : 27 - 2 = 25 ∧ ¬ Nat.Prime 27 ∧ ¬ Nat.Prime 25 := by 
  constructor
  . norm_num
  constructor
  . norm_num [Nat.Prime]
  . norm_num [Nat.Prime]