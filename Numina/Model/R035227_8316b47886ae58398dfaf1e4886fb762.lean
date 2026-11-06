import Mathlib

open Nat

theorem algebra_19929 :
    IsLeast {n | 2 < n ∧ 2 ≡ n [MOD 3] ∧ 2 ≡ n [MOD 4] ∧ 2 ≡ n [MOD 5] ∧ 2 ≡ n [MOD 6]} 62 := by

  constructor
  · -- Show that 62 is indeed in the set
    constructor
    · -- Show 62 > 2
      norm_num
    constructor
    · -- Check 2 ≡ 62 [MOD 3]
      native_decide
    constructor
    · -- Check 2 ≡ 62 [MOD 4]
      native_decide
    constructor
    · -- Check 2 ≡ 62 [MOD 5]
      native_decide
    · -- Check 2 ≡ 62 [MOD 6]
      native_decide
  · -- Now, prove that 62 is the smallest
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4, hn5⟩
    norm_num [Nat.ModEq] at hn2 hn3 hn4 hn5
    by_contra h
    push_neg at h
    interval_cases n <;> omega