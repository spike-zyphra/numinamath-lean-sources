import Mathlib

theorem number_theory_3009 :
    IsGreatest {n | n ≥ 10000 ∧ n ≤ 99999 ∧ Nat.gcd n 2022 = 337} 99415 := by
  constructor
  · -- Show 99415 satisfies the conditions
    show 99415 ≥ 10000 ∧ 99415 ≤ 99999 ∧ Nat.gcd 99415 2022 = 337
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num [Nat.gcd]
  · -- Show that for all n in the set, n ≤ 99415
    intro n hn
    rcases hn with ⟨hn1, hn2, hngcd⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.gcd] at hngcd <;> all_goals omega