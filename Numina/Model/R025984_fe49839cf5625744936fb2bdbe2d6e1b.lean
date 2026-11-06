import Mathlib

def isGood (n : ℕ) : Prop :=
  n > 0 ∧ n % (Nat.digits 10 n).sum = 22

theorem number_theory_246667 :
    IsLeast {n | isGood n} 689 := by
  constructor
  · -- Show that 689 is a good number
    show isGood 689
    constructor
    · norm_num
    · norm_num
  · -- Show that no smaller number is good
    intro n hn
    rcases hn with ⟨hn_pos, hn_mod⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_pos hn_mod <;> try { contradiction }