import Mathlib

theorem number_theory_22940 :
    IsLeast {n | n ≥ 10000 ∧ (Nat.digits 10 n).length = 5 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ 11 ∣ n} 10901 := by 
  constructor
  · -- Show 10901 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that any n in the set is ≥ 10901
    intro n hn
    rcases hn with ⟨h1, h2, h3, h4⟩
    by_contra h
    push_neg at h 
    have h5 : n < 10901 := by linarith
    interval_cases n <;> norm_num at h1 h2 h3 h4 ⊢
    <;> omega