import Mathlib

theorem number_theory_611149 :
    IsLeast {n : ℕ | 0 < n ∧ 100 ∣ ∑ i ∈ Finset.Icc 1 n, i ^ 2} 24 := by
  constructor
  · -- Show that 24 is in the set
    constructor
    · -- Show that 0 < 24
      norm_num
    · -- Show that 100 divides the sum of squares from 1 to 24
      native_decide
  · -- Show that 24 is minimal
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n < 24 := by linarith
    interval_cases n <;> try { contradiction }