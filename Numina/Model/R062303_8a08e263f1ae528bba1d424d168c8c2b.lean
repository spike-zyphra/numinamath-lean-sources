import Mathlib

theorem number_theory_6490 (x : ℕ) (hx : 3 * x ≡ 8 [MOD 13]) :
    IsLeast {x | 100 ≤ x ∧ Odd x ∧ 3 * x ≡ 8 [MOD 13]} 111 := by 
  constructor
  · -- Show that 111 is in the set
    constructor
    · norm_num
    constructor
    · decide
    · -- Show that 3 * 111 ≡ 8 [MOD 13]
      norm_num [Nat.ModEq] at hx ⊢ 
      all_goals norm_num [Nat.ModEq] at hx ⊢ 
      all_goals tauto 
  · -- Show that 111 is the smallest
    intro y hy 
    rcases hy with ⟨hy1, hy2, hy3⟩ 
    by_contra h
    push_neg at h 
    interval_cases y <;> norm_num [Nat.ModEq, Nat.odd_iff] at hy1 hy2 hy3 <;> norm_num [Nat.ModEq] at hx ⊢ <;> try { contradiction } <;> omega 
    all_goals norm_num [Nat.ModEq, Nat.odd_iff] at hy1 hy2 hy3 <;> norm_num [Nat.ModEq] at hx ⊢ <;> try { contradiction } <;> omega