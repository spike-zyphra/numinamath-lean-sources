import Mathlib

theorem algebra_16640 : IsGreatest {n | n < 100 ∧ Nat.gcd n 12 = 4} 92 := by
  constructor
  · -- Show that 92 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that 92 is the greatest
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.gcd] at hn2 <;> omega