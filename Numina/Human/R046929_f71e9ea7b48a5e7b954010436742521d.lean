import Mathlib

open Real
/-Given a=logb 8 5, b=logb 4 3, c=2/3. Then the size relationship of a,b and c is 
b > a > c-/
theorem algebra_318021 {a b c : ℝ} (ha : a = logb 8 5) (hb : b = logb 4 3)
    (hc : c = 2 / 3) : b > a ∧ a > c := by 

  -- first we prove b > a step by step --
  have h1 : b > a := by
    rw [hb, ha]
    -- plug a, b into the h1 --
    have h1 : logb 4 3 > logb 8 5 := by
      -- simplify the logb --
      have h2 : logb 4 3 = log 3 / log 4 := by 
        field_simp [logb]
      have h3 : logb 8 5 = log 5 / log 8 := by 
        field_simp [logb]
      rw [h2, h3]
      have h4 : log 4 = 2 * log 2 := by 
        calc
          log 4 = log (2^2) := by norm_num
          _ = 2 * log 2 := by simp [log_pow]
      have h5 : log 8 = 3 * log 2 := by 
        calc
          log 8 = log (2^3) := by norm_num
          _ = 3 * log 2 := by simp [log_pow]
      rw [h4, h5]
      have h6 : log 2 > 0 := by 
        apply log_pos
        norm_num
      have h7 : log 3 / (2 * log 2) > log 5 / (3 * log 2) := by
        have h8 : log 3 > 0 := by 
          apply log_pos
          norm_num
        have h9 : log 5 > 0 := by 
          apply log_pos
          norm_num
        have h10 : 3 * log 3 > 2 * log 5 := by
          have h11 : log 27 > log 25 := by 
            have h12 : log 27 = log (25 * (27 / 25)) := by 
              norm_num
            rw [h12]
            have h13 : log (25 * (27 / 25)) = log 25 + log (27 / 25) := by 
              rw [log_mul (by norm_num) (by norm_num)]
            rw [h13]
            have h14 : log (27 / 25) > 0 := by 
              apply log_pos
              norm_num 
            have h15 : log 25 > 0 := by 
              apply log_pos
              norm_num
            linarith [h14, h15]
          have h14 : log 27 = 3 * log 3 := by 
            calc 
              log 27 = log (3 ^ 3) := by norm_num
              _ = 3 * log 3 := by simp [log_pow]
          have h15 : log 25 = 2 * log 5 := by 
            calc 
              log 25 = log (5 ^ 2) := by norm_num
              _ = 2 * log 5 := by simp [log_pow]
          linarith [h14, h15, h11]
        have h11 : log 3 / (2 * log 2) > log 5 / (3 * log 2) := by
          have h12 : log 2 > 0 := h6
          have h13 : 2 * log 2 > 0 := by linarith
          have h14 : 3 * log 2 > 0 := by linarith
          have h15 : log 3 / (2 * log 2) - log 5 / (3 * log 2) > 0 := by
            have h16 : log 3 / (2 * log 2) - log 5 / (3 * log 2) = (3 * log 3 - 2 * log 5) / (6 * log 2) := by 
              field_simp
              ring
            rw [h16]
            have h17 : 3 * log 3 - 2 * log 5 > 0 := by linarith [h10]
            have h18 : 6 * log 2 > 0 := by linarith [h6]
            apply div_pos
            all_goals linarith
          linarith
        linarith [h11]
      linarith
    linarith [h1]

  -- then we prove a > c step by step --
  have h2 : a > c := by
    rw [ha, hc]
    have h2 : logb 8 5 > (2 / 3 : ℝ) := by 
      have h3 : logb 8 5 = log 5 / log 8 := by 
        field_simp [logb]
      rw [h3]
      have h4 : log 8 = 3 * log 2 := by 
        calc 
          log 8 = log (2^3) := by norm_num
          _ = 3 * log 2 := by simp [log_pow]
      rw [h4]
      have h5 : log 2 > 0 := by 
        apply log_pos
        norm_num
      have h6 : log 5 > 2 * log 2 := by 
        have h7 : log 5 > log 4 := by 
          apply log_lt_log
          all_goals norm_num
        have h8 : log 4 = 2 * log 2 := by 
          calc 
            log 4 = log (2^2) := by norm_num 
            _ = 2 * log 2 := by simp [log_pow]
        linarith [h7, h8]
      have h7 : log 5 / (3 * log 2) > (2 / 3 : ℝ) := by
        have h8 : log 2 > 0 := h5
        have h9 : log 5 / (3 * log 2) - (2 / 3 : ℝ) > 0 := by 
          have h10 : log 5 / (3 * log 2) - (2 / 3 : ℝ) = (log 5 - 2 * log 2) / (3 * log 2) := by 
            field_simp
            ring
          rw [h10]
          have h11 : log 5 - 2 * log 2 > 0 := by linarith [h6]
          have h12 : 3 * log 2 > 0 := by linarith [h8]
          apply div_pos
          all_goals linarith
        linarith
      linarith [h7]
    linarith [h2]
  exact ⟨h1, h2⟩