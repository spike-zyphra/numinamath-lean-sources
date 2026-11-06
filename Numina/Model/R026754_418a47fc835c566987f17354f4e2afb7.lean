import Mathlib

theorem number_theory_5522 :
    IsGreatest {n | 1000 ≤ n ∧ n < 10000 ∧ Nat.gcd n 1554 = 259} 9583 := by
  constructor
  · -- Show that 9583 belongs to the set
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num [Nat.gcd]
  · -- Show that 9583 is the greatest element in the set
    intro n hn
    rcases hn with ⟨h1, h2, h3⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.gcd] at h3 ⊢
    all_goals omega