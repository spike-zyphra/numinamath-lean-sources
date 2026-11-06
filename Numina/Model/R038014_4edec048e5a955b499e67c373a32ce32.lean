import Mathlib

theorem number_theory_203060 : IsGreatest {n | n < 1000} 999 ∧ 1000 - 999 = 1 := by
  constructor
  · -- Prove that 999 is the greatest in the set {n | n < 1000}
    constructor
    · -- Show that 999 is in the set
      show 999 < 1000
      all_goals norm_num
    · -- Show that for any n in the set, n ≤ 999
      intro n hn
      have h : n < 1000 := by
        simpa using hn
      have h2 : n ≤ 999 := by
        omega
      linarith
  · -- Show that 1000 - 999 = 1
    all_goals norm_num