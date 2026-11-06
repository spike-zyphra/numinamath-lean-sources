import Mathlib

theorem number_theory_241392 :
    IsGreatest {n | n^200 < 5^300} (11) := by
  constructor
  · -- Show that 11 is in the set
    norm_num
  · -- Show that for any n in the set, n ≤ 11
    intro n hn
    have h1 : n ^ 200 < 5 ^ 300 := hn
    by_contra h
    push_neg at h
    have h2 : n ≥ 12 := by omega
    have h3 : n ^ 200 ≥ 12 ^ 200 := by
      apply Nat.pow_le_pow_of_le_left
      linarith
    have h4 : 12 ^ 200 > 5 ^ 300 := by
      norm_num
    linarith