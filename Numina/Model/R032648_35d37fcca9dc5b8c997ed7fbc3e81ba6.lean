import Mathlib

theorem number_theory_12741 :
IsLeast {n | n ≤ 999 ∧ 100 ≤ n ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧
Nat.digits 10 (101 * n) ≠ List.reverse (Nat.digits 10 (101 * n))} 505 := by
  constructor
  · -- Show that 505 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · native_decide
    · native_decide
  · -- Show that any other element in the set is larger
    intro n hn
    rcases hn with ⟨h1, h2, hp, hp2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hp hp2 h1 h2 ⊢
    <;> try { contradiction }