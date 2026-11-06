import Mathlib

theorem algebra_4500 (a b c : ℤ) : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c = 44 ∧ a * c + b * c = 23 ↔
    (a = 21 ∧ b = 2 ∧ c = 1) ∨ (a = 1 ∧ b = 22 ∧ c = 1) := by
  constructor
  · -- Assume the system is satisfied, prove the solutions
    rintro ⟨ha, hb, hc, h1, h2⟩
    have eq1 : b * (a + c) = 44 := by 
      linarith
    have eq2 : c * (a + b) = 23 := by
      linarith
    have hc1 : c = 1 ∨ c = 23 := by 
      have h4 : c ∣ 23 := by 
        use a + b 
        linarith [eq2]
      have h5 : c ≤ 23 := by 
        exact Int.le_of_dvd (by norm_num) h4
      have h6 : c ≥ 1 := by 
        omega 
      interval_cases c <;> norm_num at h4 <;> tauto 
    rcases hc1 with hc1 | hc1 
    · -- Case c = 1 
      have hc1' : c = 1 := hc1 
      have h3 : a + b = 23 := by 
        rw [hc1'] at eq2 
        nlinarith 
      have h4 : b * (a + 1) = 44 := by 
        rw [hc1'] at eq1 
        nlinarith 
      have h5 : b = 22 ∨ b = 2 := by
        have h1 : b ≥ 1 := by
          omega
        have h2 : b ≤ 22 := by
          nlinarith [h4]
        interval_cases b <;> omega 
      rcases h5 with h5 | h5 
      · -- Case b = 22 
        have h6 : a = 1 := by 
          omega
        right 
        exact ⟨by omega, by omega, by omega⟩ 
      · -- Case b = 2 
        have h6 : a = 21 := by 
          omega 
        left 
        exact ⟨by omega, by omega, by omega⟩ 
    · -- Case c = 23 
      have hc1' : c = 23 := hc1 
      have h7 : a + b = 1 := by 
        rw [hc1'] at eq2 
        nlinarith 
      have h8 : a ≥ 1 := by
        omega 
      have h9 : b ≥ 1 := by 
        omega 
      nlinarith 
  · -- Assume one of the solutions, prove the system 
    rintro (h | h) 
    · -- Case (21, 2, 1) 
      rcases h with ⟨ha, hb, hc⟩ 
      constructor 
      · -- Show a > 0 
        linarith 
      constructor 
      · -- Show b > 0 
        linarith 
      constructor 
      · -- Show c > 0 
        linarith 
      constructor 
      · -- Show ab + bc = 44 
        rw [ha, hb, hc] 
        all_goals norm_num 
      · -- Show ac + bc = 23 
        rw [ha, hb, hc] 
        all_goals norm_num 
    · -- Case (1, 22, 1) 
      rcases h with ⟨ha, hb, hc⟩ 
      constructor 
      · -- Show a > 0 
        linarith 
      constructor 
      · -- Show b > 0 
        linarith 
      constructor 
      · -- Show c > 0 
        linarith 
      constructor 
      · -- Show ab + bc = 44 
        rw [ha, hb, hc] 
        all_goals norm_num 
      · -- Show ac + bc = 23 
        rw [ha, hb, hc] 
        all_goals norm_num