import Mathlib

theorem number_theory_136838 (n : ℤ) : n + 2 ∣ n ^ 2 + 3 ↔ n = -9 ∨ n = -3 ∨ n = -1 ∨ n = 5 := by
  constructor
  · -- Assume n + 2 divides n^2 + 3, prove n = -9 ∨ n = -3 ∨ n = -1 ∨ n = 5
    intro h 
    have h1 : n + 2 ∣ n ^ 2 + 3 := h 
    have h2 : n + 2 ∣ 7 := by
      have h3 : n + 2 ∣ n ^ 2 + 3 := h1 
      have h4 : n + 2 ∣ (n + 2) * (n - 2) := by 
        apply dvd_mul_right 
      have h5 : n + 2 ∣ (n ^ 2 + 3 - (n + 2) * (n - 2)) := by 
        apply Dvd.dvd.sub 
        · exact h3 
        · exact h4 
      have h7 : (n ^ 2 + 3 - (n + 2) * (n - 2)) = 7 := by
        ring 
      rw [h7] at h5 
      exact h5 
    have h4 : n + 2 = 1 ∨ n + 2 = -1 ∨ n + 2 = 7 ∨ n + 2 = -7 := by
      have h5 : n + 2 ∣ 7 := h2 
      have h6 : n + 2 ≤ 7 := by 
        apply Int.le_of_dvd (by norm_num) h5 
      have h7 : n + 2 ≥ -7 := by 
        have h8 : (- (n + 2)) ∣ 7 := by
          exact Int.neg_dvd.2 h5 
        have h9 : - (n + 2) ≤ 7 := by 
          apply Int.le_of_dvd (by norm_num) h8 
        linarith 
      interval_cases h8 : n + 2 <;> tauto 
    cases h4 with
    | inl h5 =>
      -- n + 2 = 1, so n = -1
      have : n = -1 := by linarith 
      right 
      right 
      left 
      linarith 
    | inr h5 =>
      cases h5 with
      | inl h5 =>
        -- n + 2 = -1, so n = -3
        have : n = -3 := by linarith 
        right 
        left 
        linarith 
      | inr h5 =>
        cases h5 with
        | inl h5 =>
          -- n + 2 = 7, so n = 5
          have : n = 5 := by linarith 
          right 
          right 
          right 
          linarith 
        | inr h5 =>
          -- n + 2 = -7, so n = -9
          have : n = -9 := by linarith 
          left 
          linarith 
  · -- Now the reverse direction
    rintro (h | h | h | h)
    · -- n = -9
      rw [show n = -9 by linarith]
      norm_num 
    · -- n = -3
      rw [show n = -3 by linarith]
      norm_num 
    · -- n = -1
      rw [show n = -1 by linarith]
      norm_num 
    · -- n = 5
      rw [show n = 5 by linarith]
      norm_num