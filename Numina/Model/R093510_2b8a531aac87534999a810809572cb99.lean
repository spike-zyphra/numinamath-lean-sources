import Mathlib

def is_special (N : ℕ) : Prop :=
  N > 1 ∧ (Nat.digits 8 N).headI = 1 ∧ (Nat.digits 9 N).headI = 1 ∧
  (Nat.digits 8 N).tail.reverse.headI = 1 ∧ (Nat.digits 9 N).tail.reverse.headI = 1

theorem number_theory_80008 :
    IsLeast {N | is_special N} 793 := by 
  constructor
  · -- Show that 793 is indeed special
    show is_special 793
    constructor
    · norm_num
    constructor
    · native_decide
    constructor
    · native_decide
    constructor
    · native_decide
    · native_decide
  · -- Show that 793 is the smallest
    intro N h
    rcases h with ⟨hN1, h8h, h9h, h8l, h9l⟩
    by_contra h'
    push_neg at h'
    interval_cases N <;> norm_num at h8h h8l h9h h9l hN1 <;> all_goals
      try { contradiction } <;> try { norm_num }
      <;> try { contradiction } <;> try { tauto }