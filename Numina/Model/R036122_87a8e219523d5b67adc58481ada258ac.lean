import Mathlib

theorem number_theory_202988 :
    IsLeast {n | n > (Nat.digits 10 n).sum ∧ n = (Nat.digits 10 n).sum + 1755} 1770 := by
  constructor
  · -- Show 1770 is in the set
    constructor
    · -- Show that 1770 > sum of its digits
      norm_num
    · -- Show that 1770 = sum of its digits + 1755
      norm_num 
  · -- Show that 1770 is the least 
    intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    push_neg at h 
    have h4 : n ≥ 1755 := by 
      omega 
    interval_cases n <;> norm_num at h1 h2 ⊢ <;> all_goals 
      try { contradiction }
      <;> try { omega }
      <;> try { tauto }