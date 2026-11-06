import Mathlib

theorem number_theory_47011 (n : ℕ) (h : n > 0) :
    734851474594578436096 = n ^ 6 ↔ n = 3004 := by
  constructor
  · -- Assume 734851474594578436096 = n^6, prove n = 3004
    intro h_eq
    have h1 : n ^ 6 = 734851474594578436096 := by
      linarith
    have h2 : n ≤ 3004 := by
      by_contra h3
      push_neg at h3
      have h4 : n ^ 6 > 734851474594578436096 := by
        have h5 : n ≥ 3005 := by omega
        have h6 : n ^ 6 ≥ 3005 ^ 6 := by
          exact Nat.pow_le_pow_of_le_left (by omega) 6
        have h9 : 3005 ^ 6 > 734851474594578436096 := by norm_num
        linarith [h6, h9]
      linarith [h1, h4]
    have h3 : n ≥ 3004 := by
      by_contra h4
      push_neg at h4
      have h4 : n ≤ 3003 := by omega
      have h5 : n ^ 6 ≤ 3003 ^ 6 := by
        have h6 : n ≤ 3003 := by assumption
        exact Nat.pow_le_pow_of_le_left (by omega) 6
      have h8 : 3003 ^ 6 < 734851474594578436096 := by norm_num
      linarith [h1, h5, h8]
    have h4 : n = 3004 := by
      linarith
    exact h4
  · -- Assume n = 3004, prove 734851474594578436096 = n^6
    intro h_eq
    rw [h_eq]
    all_goals
      norm_num