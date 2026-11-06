import Mathlib

theorem number_theory_13654 : IsGreatest {a | a^7 ≤ 6^15} 46 := by 
  constructor
  · -- First part: show that 46 is in the set, so 46^7 ≤ 6^15
    norm_num
  · -- Second part: showing that any a in the set is ≤ 46
    intro a
    intro ha
    have h : a ^ 7 ≤ 6 ^ 15 := by 
      simpa using ha
    by_contra h'
    push_neg at h'
    have h2 : a ≥ 47 := by
      omega
    have h3 : a ^ 7 ≥ 47 ^ 7 := by
      apply Nat.pow_le_pow_of_le_left 
      linarith
      all_goals linarith
    have h4 : 47 ^ 7 > 6 ^ 15 := by
      norm_num
    linarith
    all_goals nlinarith
    all_goals linarith