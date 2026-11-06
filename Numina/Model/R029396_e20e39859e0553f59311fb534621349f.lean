import Mathlib
theorem number_theory_98659 :
IsGreatest {n | n < 1000 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ Nat.digits 8 n = List.reverse (Nat.digits 8 n)} 585 := by
  constructor
  · -- Show that 585 is in the set
    constructor
    · -- Show that 585 < 1000
      norm_num
    constructor
    · -- Show that Nat.digits 10 585 = List.reverse (Nat.digits 10 585)
      norm_num
    · -- Show that Nat.digits 8 585 = List.reverse (Nat.digits 8 585)
      norm_num
  · -- Show that for any n in the set, n ≤ 585
    intro n hn
    rcases hn with ⟨h1, h2, h3⟩
    by_contra h
    push_neg at h
    have h4 : n < 1000 := h1
    interval_cases n <;> norm_num at h1 h2 h3 <;> all_goals
      contradiction