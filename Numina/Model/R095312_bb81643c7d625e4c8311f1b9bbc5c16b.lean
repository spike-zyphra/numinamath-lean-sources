import Mathlib

theorem number_theory_198842 :
    IsLeast {n | n ≥ 1000 ∧ ∃ k, (n * 21) = k ^ 2} 1029 := by
  constructor
  · -- 1029 is in the set: 1029 ≥ 1000 and exists k = 147
    constructor
    · -- Show n ≥ 1000
      norm_num
    · -- Show existence of k
      use 147
      all_goals norm_num
  · -- Show that 1029 is the smallest
    rintro n ⟨hn, k, hk⟩
    by_contra h
    push_neg at h
    have h1 : n < 1029 := by
      linarith
    have h2 : k ^ 2 = n * 21 := by
      linarith
    have h4 : k < 147 := by
      nlinarith [show k ^ 2 < 147 ^ 2 by
        have hn2 : n ≤ 1028 := by
          omega
        have h3 : n * 21 ≤ 1028 * 21 := by
          nlinarith
        nlinarith
      ]
    interval_cases k <;> omega