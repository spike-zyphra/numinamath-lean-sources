import Mathlib

theorem number_theory_290234 :
    IsGreatest {n | 200 < n ∧ n < 250 ∧ ∃ k, k^2 = 12 * n} 243 := by
  constructor
  · -- Prove that 243 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Let k = 54
      use 54
      all_goals norm_num
  · -- Show that 243 is greatest in the set
    intro n hn
    rcases hn with ⟨h1, h2, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h4 : k > 54 := by
      nlinarith
    have h5 : k < 55 := by
      nlinarith
    omega