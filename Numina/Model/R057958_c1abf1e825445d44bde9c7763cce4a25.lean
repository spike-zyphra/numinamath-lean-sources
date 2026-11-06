import Mathlib

theorem number_theory_6525 : IsGreatest {n | 1000 ≤ n ∧ n < 10000 ∧ Nat.gcd n 1746 = 194} 9700 := by
  constructor
  · -- Show 9700 is in the set
    show 1000 ≤ 9700 ∧ 9700 < 10000 ∧ Nat.gcd 9700 1746 = 194
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Verify gcd of 9700 and 1746 is 194
      norm_num [Nat.gcd]
  · -- Show 9700 is the greatest element
    intro n hn
    rcases hn with ⟨h1, h2, h3⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.gcd] at h3 <;> omega