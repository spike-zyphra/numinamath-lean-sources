import Mathlib

theorem number_theory_11834 : IsGreatest {n : ℤ | n < 100000 ∧ 5 ∣ 8 * (n - 2) ^ 5 - n ^ 2 + 14 * n - 24} 99997 := by
  constructor
  · -- Show 99997 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show no integer greater than 99997 is in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have h2 : n ≥ 99998 := by linarith
    have h3 : n < 100000 := hn1
    have h4 : n = 99998 ∨ n = 99999 := by
      omega
    rcases h4 with (r | r)
    · -- Case n = 99998
      rw [r] at hn2
      norm_num at hn2
      all_goals omega
    · -- Case n = 99999
      rw [r] at hn2
      norm_num at hn2
      all_goals omega