import Mathlib

theorem number_theory_608165 :
    IsLeast {n : ℤ | 0 < n ∧ ∃ a b, 17 * a + 6 * b = 13 ∧ n = a - b} 17 := by
  constructor
  · -- Show that 17 is in the set.
    constructor
    · -- Show that 17 is positive.
      norm_num
    · -- Show that there exist a and b such that 17*a + 6*b = 13 and 17 = a - b
      use 5, -12
      all_goals norm_num
  · -- Show that no integer less than 17 is in the set.
    intro n hn
    rcases hn with ⟨hn_pos, ⟨a, b, h_eq, hn_eq⟩⟩
    by_contra h
    push_neg at h
    have h1 : n < 17 := h
    have h2 : n = a - b := by linarith [hn_eq]
    have h3 : 17 * a + 6 * b = 13 := h_eq
    have h4 : b = a - n := by
      omega
    rw [h4] at h3
    omega