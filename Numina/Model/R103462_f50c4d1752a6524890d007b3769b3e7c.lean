import Mathlib

theorem algebra_9627 : IsLeast {n | 0 < n ∧ n = round (Real.logb 9 2023)} 3 := by
  constructor
  · constructor
    · norm_num
    · -- Show that 3 = round (Real.logb 9 2023)
      have h1 : round (Real.logb 9 2023) = 3 := by 
        have h2 : Real.logb 9 2023 < (3.5 : ℝ) := by 
          have h3 : Real.logb 9 2023 = Real.log 2023 / Real.log 9 := by
            field_simp [Real.logb]
          rw [h3]
          have h4 : Real.log 2023 < (3.5 : ℝ) * Real.log 9 := by
            have h5 : Real.log 2023 < Real.log 2187 := by
              apply Real.log_lt_log
              all_goals norm_num
            have h6 : Real.log 2187 = (3.5 : ℝ) * Real.log 9 := by
              have h7 : (2187 : ℝ) = 9 ^ (3 : ℝ) * (3 : ℝ) := by norm_num
              have h8 : Real.log 2187 = Real.log (9 ^ (3 : ℝ) * (3 : ℝ)) := by
                rw [h7]
              rw [h8]
              have h9 : Real.log (9 ^ (3 : ℝ) * (3 : ℝ)) = Real.log (9 ^ (3 : ℝ)) + Real.log (3 : ℝ) := by 
                rw [Real.log_mul (by positivity) (by positivity)]
              rw [h9]
              have h10 : Real.log (9 ^ (3 : ℝ)) = (3 : ℝ) * Real.log 9 := by 
                simp [Real.log_rpow]
              rw [h10]
              have h11 : Real.log (3 : ℝ) = (0.5 : ℝ) * Real.log 9 := by
                have h12 : Real.log (9 : ℝ) = 2 * Real.log (3 : ℝ) := by
                  have h13 : (9 : ℝ) = 3 ^ (2 : ℝ) := by norm_num
                  rw [h13]
                  simp [Real.log_rpow]
                ring_nf at h12 ⊢
                linarith
              rw [h11]
              all_goals ring_nf
              <;> linarith
            linarith [h5, h6]
          have h8 : (0 : ℝ) < Real.log 9 := by 
            have h9 : (0 : ℝ) < (9 : ℝ) := by norm_num
            have h10 : Real.log (9 : ℝ) > Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h11 : Real.log (1 : ℝ) = 0 := Real.log_one
            linarith [h10, h11]
          have h5 : Real.log 2023 / Real.log 9 < (3.5 : ℝ) := by 
            apply (div_lt_iff₀ h8).mpr
            linarith [h4]
          exact h5
        have h6 : (3 : ℝ) < Real.logb 9 2023 := by
          have h7 : Real.logb 9 2023 = Real.log 2023 / Real.log 9 := by
            field_simp [Real.logb]
          rw [h7]
          have h8 : Real.log 9 > (0 : ℝ) := by
            have h9 : Real.log 9 > Real.log 1 := by
              apply Real.log_lt_log
              all_goals norm_num
            have h10 : Real.log (1 : ℝ) = 0 := Real.log_one
            linarith [h9, h10]
          have h9 : Real.log 2023 > (3 : ℝ) * Real.log 9 := by
            have h10 : Real.log 2023 > Real.log 729 := by 
              apply Real.log_lt_log
              all_goals norm_num
            have h11 : Real.log (729 : ℝ) = (3 : ℝ) * Real.log 9 := by
              have h12 : (729 : ℝ) = 9 ^ (3 : ℝ) := by norm_num
              rw [h12]
              simp [Real.log_rpow]
            linarith [h10, h11]
          have h10 : (3 : ℝ) < Real.log 2023 / Real.log 9 := by
            apply (lt_div_iff₀ h8).mpr
            linarith [h9]
          exact h10
        simp [round_eq]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      norm_num [h1]
  · -- Show that 3 is the least
    intro n hn
    rcases hn with ⟨hn_pos, hn_eq⟩
    have h1 : round (Real.logb 9 2023) = 3 := by 
      have h2 : Real.logb 9 2023 < (3.5 : ℝ) := by 
        have h3 : Real.logb 9 2023 = Real.log 2023 / Real.log 9 := by
          field_simp [Real.logb]
        rw [h3]
        have h4 : Real.log 2023 < (3.5 : ℝ) * Real.log 9 := by
          have h5 : Real.log 2023 < Real.log 2187 := by
            apply Real.log_lt_log
            all_goals norm_num
          have h6 : Real.log 2187 = (3.5 : ℝ) * Real.log 9 := by
            have h7 : (2187 : ℝ) = 9 ^ (3 : ℝ) * (3 : ℝ) := by norm_num
            have h8 : Real.log 2187 = Real.log (9 ^ (3 : ℝ) * (3 : ℝ)) := by
              rw [h7]
            rw [h8]
            have h9 : Real.log (9 ^ (3 : ℝ) * (3 : ℝ)) = Real.log (9 ^ (3 : ℝ)) + Real.log (3 : ℝ) := by 
              rw [Real.log_mul (by positivity) (by positivity)]
            rw [h9]
            have h10 : Real.log (9 ^ (3 : ℝ)) = (3 : ℝ) * Real.log 9 := by 
              simp [Real.log_rpow]
            rw [h10]
            have h11 : Real.log (3 : ℝ) = (0.5 : ℝ) * Real.log 9 := by
              have h12 : Real.log (9 : ℝ) = 2 * Real.log (3 : ℝ) := by
                have h13 : (9 : ℝ) = 3 ^ (2 : ℝ) := by norm_num
                rw [h13]
                simp [Real.log_rpow]
              ring_nf at h12 ⊢
              linarith
            rw [h11]
            all_goals ring_nf
            <;> linarith
          linarith [h5, h6]
        have h8 : (0 : ℝ) < Real.log 9 := by 
          have h9 : (0 : ℝ) < (9 : ℝ) := by norm_num
          have h10 : Real.log (9 : ℝ) > Real.log (1 : ℝ) := by
            apply Real.log_lt_log
            all_goals linarith
          have h11 : Real.log (1 : ℝ) = 0 := Real.log_one
          linarith [h10, h11]
        have h5 : Real.log 2023 / Real.log 9 < (3.5 : ℝ) := by 
          apply (div_lt_iff₀ h8).mpr
          linarith [h4]
        exact h5
      have h6 : (3 : ℝ) < Real.logb 9 2023 := by
        have h7 : Real.logb 9 2023 = Real.log 2023 / Real.log 9 := by
          field_simp [Real.logb]
        rw [h7]
        have h8 : Real.log 9 > (0 : ℝ) := by
          have h9 : Real.log 9 > Real.log 1 := by
            apply Real.log_lt_log
            all_goals norm_num
          have h10 : Real.log (1 : ℝ) = 0 := Real.log_one
          linarith [h9, h10]
        have h9 : Real.log 2023 > (3 : ℝ) * Real.log 9 := by
          have h10 : Real.log 2023 > Real.log 729 := by 
            apply Real.log_lt_log
            all_goals norm_num
          have h11 : Real.log (729 : ℝ) = (3 : ℝ) * Real.log 9 := by
            have h12 : (729 : ℝ) = 9 ^ (3 : ℝ) := by norm_num
            rw [h12]
            simp [Real.log_rpow]
          linarith [h10, h11]
        have h10 : (3 : ℝ) < Real.log 2023 / Real.log 9 := by
          apply (lt_div_iff₀ h8).mpr
          linarith [h9]
        exact h10
      simp [round_eq]
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    norm_num [h1] at hn_eq ⊢
    omega