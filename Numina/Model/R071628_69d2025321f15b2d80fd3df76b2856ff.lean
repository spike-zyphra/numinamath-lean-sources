import Mathlib

theorem number_theory_3103 : IsLeast {n | n ≥ 1000 ∧ Nat.gcd n 36 = 6} 1002 := by
  constructor
  · constructor
    · norm_num
    · norm_num [Nat.gcd]
  · intro n hn
    rcases hn with ⟨hn1000, hngcd⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.gcd] at hngcd <;> all_goals omega