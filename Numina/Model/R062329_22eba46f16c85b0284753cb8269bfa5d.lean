import Mathlib

theorem number_theory_6451 :
  IsGreatest {n | 1000 ≤ n ∧ n < 10000 ∧ Nat.gcd n 3132 = 261} 9657 := by
  constructor
  · -- Show 9657 is indeed in the set.
    constructor
    · -- Show that 1000 ≤ 9657.
      norm_num
    constructor
    · -- Show that 9657 < 10000.
      norm_num
    · -- Show that gcd(9657, 3132) = 261.
      norm_num [Nat.gcd]
  · -- Show there is no larger value in the set.
    intro n hn
    rcases hn with ⟨hn1, hn2, hng⟩
    by_contra h
    push_neg at h
    have h1 : n > 9657 := h
    interval_cases n <;> norm_num [Nat.gcd] at hng
    all_goals
      try linarith