import Mathlib

theorem number_theory_10091 : IsLeast {n | 0 < n ∧ (2007 * n) % 1000 = 837} 691 := by
  constructor
  · -- Show 691 is positive and in the set.
    constructor
    · norm_num -- Show that 691 > 0
    · norm_num -- Check that (2007 * 691) % 1000 = 837
  · -- Show that 691 is the smallest.
    intro n hn
    rcases hn with ⟨hn_pos, hn_cong⟩
    omega -- Solve the integer arithmetic and prove that n ≥ 691