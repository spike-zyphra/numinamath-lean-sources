import Mathlib

theorem number_theory_291002 : ¬ Nat.Prime ((5^125 - 1) / (5^25 - 1)) := by
  norm_num [Nat.Prime]