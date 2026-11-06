import Mathlib

open Real Set

theorem algebra_214623 (a : ℝ) (ha : 0 < a ∧ a ≠ 1) :
    logb a (2 / 3) < 1 ↔ (0 < a ∧ a < 2 / 3) ∨ (1 < a) := by
  constructor
  · -- Assume logb a (2 / 3) < 1, prove (0 < a ∧ a < 2 / 3) ∨ (1 < a)
    intro h
    by_cases h1 : a > 1
    · -- If a > 1, then the right side must be true
      right
      tauto 
    · -- If not a > 1, then a < 1
      have h2 : a < 1 := by 
        by_contra h'
        push_neg at h'
        have : a = 1 := by 
          linarith 
        tauto 
      have h3 : logb a (2 / 3) < 1 := h 
      have h4 : logb a (2 / 3) = (log (2 / 3) ) / (log a) := by 
        field_simp [logb]
      rw [h4] at h 
      have h5 : log a < 0 := by 
        have h1 : 0 < a := ha.1 
        have h2 : a < 1 := by linarith 
        have h5 : log a < 0 := by 
          have h6 : log a < log (1 : ℝ) := by 
            apply Real.log_lt_log 
            all_goals linarith 
          have h7 : log (1 : ℝ) = 0 := Real.log_one 
          linarith 
        linarith 
      have h6 : log (2 / 3) > log a := by 
        have h5' : log a < 0 := h5 
        have h7 : log (2 / 3) / log a < (1 : ℝ) := by 
          linarith 
        have h8 : log (2 / 3) > log a := by 
          have h10 : log a < 0 := h5 
          apply (div_lt_iff_of_neg' (by linarith)).mp at h7
          linarith 
        linarith 
      have h7 : a < (2 / 3 : ℝ) := by 
        by_contra h8 
        push_neg at h8 
        have h8' : log a ≥ log (2 / 3) := by
          have h9 : 0 < a := ha.1 
          have h10 : 0 < (2 / 3 : ℝ) := by norm_num 
          have h11 : a ≥ (2 / 3 : ℝ) := by linarith 
          have h12 : log a ≥ log (2 / 3) := by
            apply Real.log_le_log 
            all_goals linarith 
          linarith 
        linarith 
      left 
      constructor <;> linarith 
  · -- Assume (0 < a ∧ a < 2 / 3) ∨ (1 < a), prove logb a (2 / 3) < 1
    rintro (h | h)
    · -- Case (0 < a ∧ a < 2 / 3)
      rcases h with ⟨ha1, ha2⟩ 
      have h1 : a < 1 := by linarith 
      have h2 : logb a (2 / 3) < 1 := by
        have h3 : logb a (2 / 3) = (log (2 / 3) ) / (log a) := by 
          field_simp [logb]
        rw [h3] 
        have h4 : log a < 0 := by 
          have h1 : 0 < a := ha1 
          have h5 : a < 1 := by linarith 
          have h4 : log a < 0 := by 
            have h6 : log a < log (1 : ℝ) := by 
              apply Real.log_lt_log 
              all_goals linarith 
            have h7 : log (1 : ℝ) = 0 := Real.log_one 
            linarith 
          linarith 
        have h5 : log (2 / 3) > log a := by 
          have h6 : a < (2 / 3 : ℝ) := by linarith 
          have h7 : 0 < a := ha1 
          have h8 : 0 < (2 / 3 : ℝ) := by norm_num 
          have h5 : log a < log (2 / 3) := by 
            apply Real.log_lt_log 
            all_goals linarith 
          linarith 
        apply (div_lt_iff_of_neg' (by linarith)).mpr 
        linarith 
      linarith 
    · -- Case (1 < a)
      have h1 : a > 1 := h 
      have h2 : logb a (2 / 3) < 1 := by
        have h3 : logb a (2 / 3) = (log (2 / 3) ) / (log a) := by 
          field_simp [logb]
        rw [h3] 
        have h4 : log a > 0 := by 
          have h1 : 1 < a := h 
          have h4 : log a > 0 := by 
            have h5 : log a > log (1 : ℝ) := by 
              apply Real.log_lt_log 
              all_goals linarith 
            have h6 : log (1 : ℝ) = 0 := Real.log_one 
            linarith 
          linarith 
        have h5 : log (2 / 3) < log a := by 
          have h1 : 2 / 3 < a := by 
            nlinarith [h] 
          have h6 : log (2 / 3) < log a := by 
            apply Real.log_lt_log 
            all_goals linarith 
          linarith 
        apply (div_lt_iff' (by linarith)).mpr 
        linarith 
      linarith