import Mathlib

theorem number_theory_13707 : IsLeast {n : ℕ+ | (n.val.divisors.filter Odd).card = 6 ∧
    (n.val.divisors.filter Even).card = 12} 180 := by
  constructor
  · -- Show that 180 is in the set.
    constructor
    · native_decide
    · native_decide
  · -- Show that 180 is the smallest element in the set.
    intro n hn
    rcases hn with ⟨h1, h2⟩
    have h3 : n.val ≥ 180 := by
      by_contra h
      push_neg at h
      have h4 : n.val < 180 := h
      have h5 : n.val < 180 := h4
      interval_cases h : n.val <;> norm_num at h1 h2 ⊢ <;> try { contradiction }
    exact_mod_cast h3