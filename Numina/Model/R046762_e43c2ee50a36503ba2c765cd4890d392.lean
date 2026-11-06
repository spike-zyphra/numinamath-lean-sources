import Mathlib

theorem number_theory_98903 :
    IsLeast {n | n^3 ≡ 2016 [MOD 10000]} 856 := by
  constructor
  · -- Show that 856 is in the set
    norm_num [Nat.ModEq]
  · -- Show that 856 is the smallest element in the set
    intro n hn
    norm_num [Nat.ModEq] at hn ⊢
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn ⊢
    <;> omega