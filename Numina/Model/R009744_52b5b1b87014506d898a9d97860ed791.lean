import Mathlib

theorem number_theory_114525 : ¬ Nat.Prime ((5^125 - 1) / (5^25 - 1)) := by
  norm_num [Nat.Prime]
  <;> native_decide
  all_goals trivial