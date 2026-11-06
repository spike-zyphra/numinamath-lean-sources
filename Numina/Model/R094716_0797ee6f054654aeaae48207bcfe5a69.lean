import Mathlib

theorem number_theory_12132 (n m : ℕ) (h₀ : n > 0) (h₁ : m > 0)
    (h₂ : 210 = n * (n + 1)) (h₃ : 210 = m * (m + 1) * (m + 2)) :
    n + m + (n + 1) + (m + 1) + (m + 2) = 47 := by

  have h4 : n ≤ 14 := by
    by_contra h
    push_neg at h
    have h5 : n * (n + 1) > 210 := by
      nlinarith
      all_goals linarith
    linarith [h₂, h5]

  have hn : n = 14 := by
    interval_cases n <;> omega

  have h6 : m ≤ 6 := by 
    by_contra h
    push_neg at h
    have h7 : m * (m + 1) * (m + 2) > 210 := by
      have hm1 : m ≥ 7 := by linarith
      have hm2 : m + 1 ≥ 8 := by linarith
      have hm3 : m + 2 ≥ 9 := by linarith
      have h8 : m * (m + 1) * (m + 2) ≥ 7 * 8 * 9 := by 
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        all_goals linarith
        all_goals linarith
      norm_num at h8 ⊢
      linarith
    linarith [h₃, h7]

  have hm : m = 5 := by
    interval_cases m <;> omega

  calc 
    n + m + (n + 1) + (m + 1) + (m + 2) = 14 + 5 + (14 + 1) + (5 + 1) + (5 + 2) := by 
      rw [show n = 14 by linarith [hn], show m = 5 by linarith [hm]]
    _ = 47 := by 
      all_goals omega