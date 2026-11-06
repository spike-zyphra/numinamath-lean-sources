import Mathlib

theorem inequalities_13550 :
    IsGreatest {n | n^240 ≤ 17^360} 70 := by
  constructor
  · -- Show that 70 belongs to the set
    norm_num
  · -- Show that 70 is greatest in the set
    intro n hn
    have h : n ^ 240 ≤ 17 ^ 360 := by
      simpa using hn
    by_contra h'
    push_neg at h'
    have h1 : n ≥ 71 := by linarith
    have h2 : n ^ 240 ≥ 71 ^ 240 := by
      have h' : n ≥ 71 := h1
      have h3 : n ^ 240 ≥ 71 ^ 240 := by
        apply Nat.pow_le_pow_of_le_left
        all_goals linarith
      linarith
    have h3 : (71 : ℕ) ^ 240 > 17 ^ 360 := by
      norm_num
    linarith