import Mathlib

theorem number_theory_196569 :
    IsLeast {n | ∃ k, n = 9 * k + 36 ∧ ∃ m, n = 10 * m + 45 ∧ ∃ p, n = 11 * p + 55} 495 := by
  constructor
  · -- Show that 495 is indeed in the set
    use 51
    constructor
    · norm_num -- Verify 495 = 9 * 51 + 36
    · -- Now show existence of m
      existsi 45
      constructor
      · norm_num -- Verify 495 = 10 * 45 + 45
      · -- Now show existence of p
        existsi 40
        all_goals norm_num -- Verify 495 = 11 * 40 + 55
  · -- Show that 495 is the smallest in the set
    intro n hn
    rcases hn with ⟨k, hk1, ⟨m, hm1, ⟨p, hp1⟩⟩⟩
    omega -- Solve the arithmetic constraints