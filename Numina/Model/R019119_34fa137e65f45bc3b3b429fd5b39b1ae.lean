import Mathlib

theorem number_theory_6940 :
    IsLeast {n | 0 < n ∧ (Nat.digits 10 n).prod = 400} 2558 := by
  constructor
  · -- Show 2558 is in the set
    constructor
    · norm_num
    · native_decide
  · -- Show 2558 is the least in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_prod⟩
    by_contra h
    push_neg at h
    -- Given a contradiction approach
    -- Looking into all possible numbers and their digit product computationally.
    have h1 : n ≤ 2557 := by omega
    interval_cases n <;> norm_num [Nat.digits, Nat.digitsAux] at hn_prod hn_pos ⊢ <;> try { contradiction }
    <;> try { trivial }