import Mathlib

/-The arithmetic mean of ten different natural numbers is 12.5.
What is the greatest possible value of the smallest of these numbers? Explain your answer.-/

theorem number_theory_238395: IsGreatest {a1: ℤ | ∃ a2 a3 a4 a5 a6 a7 a8 a9 a10 : ℤ,
  0 ≤ a1 ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 ∧ a4 < a5 ∧ a5 < a6 ∧ a6 < a7 ∧ a7 < a8 ∧ a8 < a9 ∧ a9 < a10 ∧
  (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10) / (10: ℚ) = 12.5} 8 := by

  constructor

  -- the forward direction
  .
    simp only [Set.mem_setOf_eq]
    use 9, 10, 11, 12, 13, 14, 15, 16, 17
    norm_num

  -- the backward direction
  .
    intro a1 h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨a2, a3, a4, a5, a6, a7, a8, a9, a10, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, h⟩ := h
    replace h: (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10) = 125 := by
      qify
      linarith
    nlinarith