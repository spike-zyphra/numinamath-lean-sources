import Mathlib

theorem number_theory_36849 :
    IsLeast {n | n ≥ 100 ∧ (∃ k, n = k^2) ∧ n % 10 ≠ 0 ∧ (∃ m, m^2 = n / 100)} 121 := by
  constructor
  · -- Show 121 is in the set.
    constructor
    · norm_num
    constructor
    · use 11
      all_goals norm_num
    constructor
    · norm_num
    · use 1
      all_goals norm_num
  · -- Show the minimality.
    intro n hn
    rcases hn with ⟨h100, ⟨k, hk⟩, h10, ⟨m, hm⟩⟩
    by_contra h
    push_neg at h
    have h2 : k ^ 2 < 121 := by
      nlinarith [show k ^ 2 = n by linarith [hk], h]
    have hk1 : k ≤ 10 := by
      nlinarith
    have hk2 : k ≥ 10 := by
      nlinarith [show k ^ 2 ≥ 100 by nlinarith [show n = k ^ 2 by linarith [hk], h100]]
    have hk10 : k = 10 := by
      omega
    have h3 : n = 100 := by
      rw [show n = k^2 by linarith [hk]]
      rw [hk10]
      all_goals norm_num
    have h4 : n % 10 = 0 := by
      rw [h3]
      all_goals norm_num
    omega