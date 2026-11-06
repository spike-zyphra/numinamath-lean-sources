import Mathlib

theorem number_theory_63211 : IsLeast {n | n ≥ 100 ∧ n ≤ 999 ∧ n = (Nat.digits 10 n).sum + 2 * (Nat.digits 10 n).prod} 397 := by 
  constructor
  · -- Show that 397 is in the set
    show 397 ≥ 100 ∧ 397 ≤ 999 ∧ 397 = (Nat.digits 10 397).sum + 2 * (Nat.digits 10 397).prod
    constructor
    · norm_num -- 397 ≥ 100
    constructor
    · norm_num -- 397 ≤ 999
    · norm_num -- 397 = sum of its digits + 2 * product of its digits
  · -- Show that 397 is the smallest in the set
    intro n hn
    rcases hn with ⟨hn100, hn999, heq⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at heq <;> all_goals omega