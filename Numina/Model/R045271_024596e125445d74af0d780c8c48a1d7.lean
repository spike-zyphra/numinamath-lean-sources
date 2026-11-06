import Mathlib

theorem number_theory_107177 : IsLeast {n | n > 1818 ∧ ∃ k, (n / 100) * (n % 100) = k ^ 2} 1832 := by
  constructor
  · -- Verify 1832 is in the set
    constructor
    · norm_num
    · use 24
      all_goals norm_num
  · -- We now prove 1832 is the smallest
    intro n hn
    rcases hn with ⟨hn1, ⟨k, hnk⟩⟩
    by_contra h
    push_neg at h
    have h1 : n > 1818 := hn1
    have h2 : n < 1832 := h
    have h3 : n / 100 = 18 := by
      interval_cases n <;> norm_num
      <;> omega
    have h4 : n % 100 < 100 := by 
      omega
    have h5 : k ^ 2 < (18 * 100) := by
      have h6 : k ^ 2 = (n / 100) * (n % 100) := by 
        linarith
      rw [h3] at h6
      nlinarith [show n % 100 < 100 by omega]
    have h42 : k ≤ 42 := by
      nlinarith
    interval_cases k <;> try { 
      omega
    }
    all_goals 
      interval_cases n <;> omega