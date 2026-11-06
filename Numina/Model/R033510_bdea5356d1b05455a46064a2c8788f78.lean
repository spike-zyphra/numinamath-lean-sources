import Mathlib

open Real

theorem algebra_167185 {x : ℝ} (hx : 0 < x ∧ x ≠ 1) :
    logb x (125 * x) * logb 25 x ^ 2 = 1 ↔ x = 1 / 625 ∨ x = 5 := by
  constructor
  · -- Forward direction: if the equation holds, then x is one of the solutions.
    intro h
    have hx1 : 0 < x := hx.1
    have hx2 : x ≠ 1 := hx.2
    have h1 : logb x (125 * x) = (logb 5 (125 * x)) / (logb 5 x) := by
      field_simp [logb]
    have h2 : logb 5 (125 * x) = logb 5 125 + logb 5 x := by
      rw [logb_mul (by norm_num) (by linarith)]
    have h3 : logb 5 125 = 3 := by
      calc
        logb 5 125 = logb 5 (5 ^ 3 : ℝ) := by norm_num
        _ = 3 := by simp [logb_pow]
    have h4 : logb 5 (125 * x) = 3 + logb 5 x := by
      rw [h2, h3]
    have h5 : logb x (125 * x) = (3 + logb 5 x) / (logb 5 x) := by
      rw [h1, h4]
    have h6 : logb 25 x = (logb 5 x) / 2 := by
      have h7 : logb 25 x = (logb 5 x) / (logb 5 (25 : ℝ)) := by
        field_simp [logb]
      have h8 : logb 5 (25 : ℝ) = 2 := by
        calc
          logb 5 (25 : ℝ) = logb 5 (5 ^ 2 : ℝ) := by norm_num
          _ = 2 := by simp [logb_pow]
      rw [h8] at h7
      linarith [h7]
    rw [h5, h6] at h
    have h7 : (3 + logb 5 x) / (logb 5 x) * (( (logb 5 x) / 2 ) ^ 2) = 1 := by
      linarith
    have h8 : (logb 5 x) ≠ 0 := by
      by_contra h9
      have h10 : logb 5 x = 0 := by linarith
      rw [h10] at h7
      norm_num at h7
    have h9 : (3 + logb 5 x) / (logb 5 x) * (( (logb 5 x) / 2 ) ^ 2) = ( (3 + logb 5 x) * (logb 5 x) ) / 4 := by
      field_simp [h8]
      <;> ring
    rw [h9] at h7
    have h10 : (3 + logb 5 x) * (logb 5 x) = 4 := by
      linarith
    have h11 : (logb 5 x) ^ 2 + 3 * (logb 5 x) - 4 = 0 := by
      nlinarith
    have h12 : (logb 5 x - 1) * (logb 5 x + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h12) with h13 h14
    · -- Case where $\log_5 x = 1$, so $x = 5$
      have h15 : logb 5 x = 1 := by linarith
      have h16 : x = 5 := by
        have h17 : x = (5 : ℝ) ^ (logb 5 x : ℝ) := by
          field_simp [Real.logb_eq_iff_rpow_eq]
        rw [h15] at h17
        norm_num at h17 ⊢
        linarith
      right
      tauto
    · -- Case where $\log_5 x = -4$, so $x = 1/625$
      have h15 : logb 5 x = -4 := by linarith
      have h16 : x = (1 / 625 : ℝ) := by
        have h17 : x = (5 : ℝ) ^ (logb 5 x : ℝ) := by
          field_simp [Real.logb_eq_iff_rpow_eq]
        rw [h15] at h17
        have h18 : x = (5 : ℝ) ^ (-4 : ℝ) := by
          linarith
        have h19 : (5 : ℝ) ^ (-4 : ℝ) = (1 / 625 : ℝ) := by
          norm_num
        rw [h19] at h18
        linarith
      left
      tauto
  · -- Backward direction: if x is one of the solutions, then the equation holds.
    rintro (h | h)
    · -- When $x = 1/625$
      rw [h]
      have h1 : logb (1 / 625 : ℝ) (125 * (1 / 625 : ℝ)) * (logb 25 (1 / 625 : ℝ)) ^ 2 = 1 := by
        have h2 : logb (1 / 625 : ℝ) (125 * (1 / 625 : ℝ) ) = 1 / 4 := by
          have h3 : logb (1 / 625 : ℝ) (125 * (1 / 625 : ℝ)) = (logb 5 (125 * (1 / 625 : ℝ)) ) / (logb 5 (1 / 625 : ℝ) ) := by
            field_simp [logb]
          have h4 : logb 5 (125 * (1 / 625 : ℝ)) = -1 := by
            have h5 : (125 * (1 / 625 : ℝ) : ℝ) = (1 / 5 : ℝ) := by
              norm_num
            rw [h5]
            calc
              logb 5 (1 / 5 : ℝ) = logb 5 (1 : ℝ) - logb 5 (5 : ℝ) := by rw [logb_div (by norm_num) (by norm_num)]
              _ = 0 - 1 := by simp
              _ = -1 := by norm_num
          have h6 : logb 5 (1 / 625 : ℝ) = -4 := by
            calc
              logb 5 (1 / 625 : ℝ) = logb 5 (1 : ℝ) - logb 5 (625 : ℝ) := by rw [logb_div (by norm_num) (by norm_num)]
              _ = 0 - logb 5 (625 : ℝ) := by simp
              _ = 0 - 4 := by
                have h7 : logb 5 (625 : ℝ) = 4 := by
                  calc
                    logb 5 (625 : ℝ) = logb 5 (5 ^ 4 : ℝ) := by norm_num
                    _ = 4 := by simp [logb_pow]
                rw [h7]
              _ = -4 := by ring
          rw [h3, h4, h6]
          all_goals norm_num
        have h3 : (logb 25 (1 / 625 : ℝ)) ^ 2 = 4 := by
          have h4 : logb 25 (1 / 625 : ℝ) = -2 := by
            have h5 : logb 25 (1 / 625 : ℝ) = (logb 5 (1 / 625 : ℝ)) / (logb 5 (25 : ℝ)) := by
              field_simp [logb]
            have h6 : logb 5 (1 / 625 : ℝ) = -4 := by
              calc
                logb 5 (1 / 625 : ℝ) = logb 5 (1 : ℝ) - logb 5 (625 : ℝ) := by rw [logb_div (by norm_num) (by norm_num)]
                _ = 0 - logb 5 (625 : ℝ) := by simp
                _ = 0 - 4 := by
                  have h7 : logb 5 (625 : ℝ) = 4 := by
                    calc
                      logb 5 (625 : ℝ) = logb 5 (5 ^ 4 : ℝ) := by norm_num
                      _ = 4 := by simp [logb_pow]
                  rw [h7]
                _ = -4 := by ring
            have h7 : logb 5 (25 : ℝ) = 2 := by
              calc
                logb 5 (25 : ℝ) = logb 5 (5 ^ 2 : ℝ) := by norm_num
                _ = 2 := by simp [logb_pow]
            rw [h6, h7] at h5
            linarith
          rw [h4]
          all_goals norm_num
        rw [h2, h3]
        all_goals norm_num
      linarith
    · -- When $x = 5$
      rw [h]
      have h1 : logb (5 : ℝ) (125 * (5 : ℝ)) * (logb 25 (5 : ℝ)) ^ 2 = 1 := by
        have h2 : logb (5 : ℝ) (125 * (5 : ℝ)) = 4 := by
          calc
            logb (5 : ℝ) (125 * (5 : ℝ)) = logb (5 : ℝ) (625 : ℝ) := by norm_num
            _ = 4 := by
              calc
                logb (5 : ℝ) (625 : ℝ) = logb (5 : ℝ) (5 ^ 4 : ℝ) := by norm_num
                _ = 4 := by simp [logb_pow]
        have h4 : (logb 25 (5 : ℝ) : ℝ) = 1 / 2 := by
          have h5 : logb 25 (5 : ℝ) = (logb 5 (5 : ℝ)) / (logb 5 (25 : ℝ) : ℝ) := by
            field_simp [logb]
          have h6 : logb 5 (5 : ℝ) = 1 := by
            rw [logb_self_eq_one]
            all_goals norm_num
          have h7 : logb 5 (25 : ℝ) = 2 := by
            calc
              logb 5 (25 : ℝ) = logb 5 (5 ^ 2 : ℝ) := by norm_num
              _ = 2 := by simp [logb_pow]
          rw [h6, h7] at h5
          linarith
        rw [h2, h4]
        all_goals norm_num
      linarith