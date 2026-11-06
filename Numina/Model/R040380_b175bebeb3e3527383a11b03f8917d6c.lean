import Mathlib

theorem algebra_20530 :
   IsLeast {n : ℕ| n > 200 ∧ Nat.gcd n 36 = 18 } 234 := by
  constructor
  · -- Show that 234 is in the set
    show 234 > 200 ∧ Nat.gcd 234 36 = 18
    constructor
    · norm_num
    · norm_num [Nat.gcd]
  · -- Show that 234 is the least in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.gcd] at hn2 ⊢