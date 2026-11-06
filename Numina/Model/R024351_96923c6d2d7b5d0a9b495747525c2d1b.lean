import Mathlib

theorem number_theory_88382 :
    IsLeast {n | 10 ≤ n ∧ Nat.Prime (n + 6) ∧ ∃ m, m^2 = 9 * n + 7} 53 := by
  constructor
  · -- Show that 53 belongs to the set.
    constructor
    · norm_num
    constructor
    · norm_num
    use 22
    all_goals norm_num
  · -- Show that 53 is indeed the smallest element.
    intro n hn
    rcases hn with ⟨hn1, h1, ⟨m, hm⟩⟩
    by_contra h
    push_neg at h
    have h2 : n < 53 := h
    have h3 : m ≤ 22 := by nlinarith
    interval_cases m <;> interval_cases n <;> norm_num at hm h1 hn1 <;> try { contradiction }
    <;> try { tauto }
    <;> try { contradiction }
    <;> try { tauto }