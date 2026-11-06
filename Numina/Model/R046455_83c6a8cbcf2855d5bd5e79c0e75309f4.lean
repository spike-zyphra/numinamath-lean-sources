import Mathlib

theorem number_theory_47448 : IsGreatest {n : ℕ | ∃m, 0 < m ∧ m < 2015 ∧ n = 2015 % m} 1007 := by
  constructor
  · -- Show that 1007 is in the set.
    use 1008
    all_goals norm_num
  · -- Show that 1007 is greatest in the set.
    intro n hn
    rcases hn with ⟨m, hm_pos, hm_lt, hn_eq⟩
    have h1 : m < 2015 := hm_lt
    have hn_eq1 : n = 2015 % m := hn_eq
    by_contra h
    push_neg at h
    have hn1007 : n > 1007 := h
    have h2 : 2015 % m > 1007 := by
      omega
    interval_cases m <;> norm_num at hn_eq1 h2 <;> omega