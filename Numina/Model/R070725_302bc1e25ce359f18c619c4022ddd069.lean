import Mathlib

theorem inequalities_200436 : IsGreatest {n | n^300 < 3^500} 6 := by
  constructor
  · -- Show that 6 indeed satisfies the inequality 6^300 < 3^500
    norm_num
  · -- Show that 6 is the greatest element in the set
    intro n hn
    have h : n ^ 300 < 3 ^ 500 := by
      simpa using hn
    by_contra h'
    push_neg at h'
    have h1 : n ≥ 7 := by linarith
    have h2 : n ^ 300 ≥ 7 ^ 300 := by
      apply Nat.pow_le_pow_of_le_left
      linarith
    have h3 : 7 ^ 300 > 3 ^ 500 := by
      norm_num
    have h4 : n ^ 300 > 3 ^ 500 := by linarith
    linarith