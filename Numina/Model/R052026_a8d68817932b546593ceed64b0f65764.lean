import Mathlib

theorem number_theory_116048 (n : ℤ) : (n + 1) ∣ (n ^ 2 + 1) ↔ n = -3 ∨ n = -2 ∨ n = 0 ∨ n = 1 := by 
  constructor
  · -- assume n + 1 | n ^ 2 + 1, prove n ∈ {-3, -2, 0, 1}
    intro h
    have h1 : (n + 1) ∣ (n ^ 2 + 1) := h
    have h2 : (n + 1) ∣ 2 := by
      -- we know that n^2 + 1 = (n + 1)(n - 1) + 2
      -- so if n + 1 | n^2 + 1, then n + 1 | 2
      have h5 : (n + 1) ∣ ((n : ℤ) ^ 2 + 1) := h
      have h6 : (n + 1) ∣ ((n + 1) * (n - 1)) := by 
        use (n - 1)
        all_goals ring_nf
        all_goals linarith
      -- using the identity: if a divides b and a divides c, then a divides b - c
      have h7 : (n + 1) ∣ ((n : ℤ) ^ 2 + 1 - ((n + 1) * (n - 1))) := by
        apply Int.dvd_sub
        · exact h5
        · exact h6
      -- simplify the expression
      have h8 : (n : ℤ) ^ 2 + 1 - ((n + 1) * (n - 1)) = 2 := by 
        ring_nf
      rw [h8] at h7
      exact h7
    have h3 : (n + 1) ∣ 2 := h2
    have h4 : (n + 1) ≤ 2 := by 
      apply Int.le_of_dvd (show (0 : ℤ) < 2 by norm_num) h3
    have h5 : (n + 1) ≥ -2 := by 
      have h6 : -(n + 1) ∣ 2 := by 
        exact Int.neg_dvd.2 h3
      have h7 : -(n + 1) ≤ 2 := by 
        apply Int.le_of_dvd (show (0 : ℤ) < 2 by norm_num) h6
      linarith
    have h8 : (n + 1) = -2 ∨ (n + 1) = -1 ∨ (n + 1) = 1 ∨ (n + 1) = 2 := by 
      interval_cases h9 : (n + 1) <;> tauto
    rcases h8 with (h9 | h9 | h9 | h9)
    · -- case where n + 1 = -2, so n = -3
      have hn : n = -3 := by linarith
      simp [hn]
    · -- case where n + 1 = -1, so n = -2
      have hn : n = -2 := by linarith
      simp [hn]
    · -- case where n + 1 = 1, so n = 0
      have hn : n = 0 := by linarith
      simp [hn]
    · -- case where n + 1 = 2, so n = 1
      have hn : n = 1 := by linarith
      simp [hn]
  · -- assume n ∈ {-3, -2, 0, 1}, prove n + 1 | n ^ 2 + 1
    rintro (h | h | h | h)
    · -- n = -3
      rw [h]
      norm_num
    · -- n = -2
      rw [h]
      norm_num
    · -- n = 0
      rw [h]
      norm_num
    · -- n = 1
      rw [h]
      norm_num