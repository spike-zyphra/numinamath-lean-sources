import Mathlib

open Real

theorem algebra_250199 {x : ℝ} (hx : x > 1) :
    x ^ (logb 3 (x - 1)) + 2 * (x - 1) ^ (logb 3 x) = 3 * x ^ 2 ↔ x = 10 := by 
  constructor
  · -- Assume the equation holds, prove x = 10
    intro h_eq
    have h1 : x ^ (logb 3 (x - 1)) = (x - 1) ^ (logb 3 x) := by
      have h2 : log (x ^ (logb 3 (x - 1))) = log ((x - 1) ^ (logb 3 x)) := by
        have h3 : log (x ^ (logb 3 (x - 1))) = logb 3 (x - 1) * log x := by
          rw [log_rpow]
          all_goals linarith
        have h4 : log ((x - 1) ^ (logb 3 x)) = logb 3 x * log (x - 1) := by
          rw [log_rpow]
          all_goals
          have : x - 1 > 0 := by
            linarith
          linarith
        rw [h3, h4]
        have h5 : logb 3 (x - 1) = (log (x - 1) ) / (log (3 : ℝ)) := by
          field_simp [logb]
        have h6 : logb 3 x = (log x ) / (log (3 : ℝ)) := by
          field_simp [logb]
        rw [h5, h6]
        field_simp [show log (3 : ℝ) ≠ 0 by apply ne_of_gt; apply Real.log_pos; all_goals norm_num]
        <;> ring
      have h3 : x ^ (logb 3 (x - 1)) > 0 := by
        apply Real.rpow_pos_of_pos
        all_goals linarith
      have h4 : (x - 1) ^ (logb 3 x) > 0 := by
        apply Real.rpow_pos_of_pos
        have h10 : x - 1 > 0 := by
          linarith
        all_goals linarith
      have h5 : x ^ (logb 3 (x - 1)) = (x - 1) ^ (logb 3 x) := by
        apply log_injOn_pos (Set.mem_Ioi.mpr (show (x ^ (logb 3 (x - 1)) : ℝ) > 0 by linarith)) (Set.mem_Ioi.mpr (show (x - 1) ^ (logb 3 x) > 0 by linarith)) h2
      exact h5
    have h8 : x ^ (logb 3 (x - 1)) = x ^ 2 := by
      have h9 : x ^ (logb 3 (x - 1)) + 2 * (x - 1) ^ (logb 3 x) = 3 * (x ^ 2) := by
        linarith [h_eq]
      have h10 : (x - 1) ^ (logb 3 x) = x ^ (logb 3 (x - 1)) := by
        linarith [h1]
      rw [h10] at h9
      have h11 : x ^ (logb 3 (x - 1)) = x ^ 2 := by
        have h12 : x ^ (logb 3 (x - 1)) + 2 * x ^ (logb 3 (x - 1)) = 3 * (x ^ 2) := by
          linarith [h9]
        have h13 : 3 * (x ^ (logb 3 (x - 1))) = 3 * (x ^ 2) := by
          nlinarith [h12]
        have h14 : x ^ (logb 3 (x - 1)) = x ^ 2 := by
          nlinarith
        exact h14
      exact h11
    have h9 : logb 3 (x - 1) = (2 : ℝ) := by
      have h7 : log (x ^ (logb 3 (x - 1)) ) = log (x ^ 2) := by
        rw [h8]
      have h10 : log (x ^ (logb 3 (x - 1)) ) = logb 3 (x - 1) * log x := by
        rw [log_rpow]
        all_goals linarith
      have h11 : log (x ^ 2) = (2 : ℝ) * log x := by
        simp [log_pow]
      rw [h10, h11] at h7
      have h13 : log x > 0 := by
        apply Real.log_pos
        all_goals linarith
      have h14 : (logb 3 (x - 1) - 2) * log x = 0 := by 
        linarith
      cases' (mul_eq_zero.mp h14) with h15 h16
      · -- Case `logb 3 (x - 1) - 2 = 0`
        linarith
      · -- Case `log x = 0`
        linarith
    have h10 : x - 1 = (9 : ℝ) := by
      have h11 : logb 3 (x - 1) = (2 : ℝ) := h9
      have h12 : x - 1 = (3 : ℝ) ^ (2 : ℝ) := by
        rw [logb_eq_iff_rpow_eq] at h11
        · -- Assume (3 : ℝ) ^ (2 : ℝ) = x - 1
          linarith
        all_goals nlinarith
      norm_num at h12 ⊢
      linarith
    linarith
  · -- Assume x = 10, prove the equation holds
    intro h_eq
    rw [h_eq]
    have h11 : logb 3 (10 - 1 : ℝ) = (2 : ℝ) := by
      rw [show (10 - 1 : ℝ) = (9 : ℝ) by norm_num]
      rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [logb_rpow]
      all_goals norm_num
    have h12 : (10 : ℝ) ^ (logb 3 (10 - 1 : ℝ)) = (100 : ℝ) := by
      rw [h11]
      norm_num
    have h13 : ( (10 - 1 : ℝ) ) ^ (logb 3 (10 : ℝ)) = (100 : ℝ) := by
      have h14 : (10 - 1 : ℝ) = (9 : ℝ) := by norm_num
      have h15 : (9 : ℝ) ^ (logb 3 (10 : ℝ)) = (100 : ℝ) := by
        have h18 : (9 : ℝ) ^ (logb 3 (10 : ℝ)) = ((3 : ℝ) ^ (2 : ℝ)) ^ (logb 3 (10 : ℝ)) := by
          norm_num
        have h19 : ((3 : ℝ) ^ (2 : ℝ)) ^ (logb 3 (10 : ℝ)) = (3 : ℝ) ^ (2 * logb 3 (10 : ℝ) ) := by 
          rw [← Real.rpow_mul]
          ring
          all_goals norm_num
        have h20 : (3 : ℝ) ^ (2 * logb 3 (10 : ℝ)) = ((3 : ℝ) ^ (logb 3 (10 : ℝ)) ) ^ 2 := by
          calc
            (3 : ℝ) ^ (2 * logb 3 (10 : ℝ)) = (3 : ℝ) ^ (2 * (logb 3 (10 : ℝ)) ) := by ring_nf
            _ = ((3 : ℝ) ^ (logb 3 (10 : ℝ)) ) ^ 2 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              ring
              all_goals norm_num
        have h21 : (3 : ℝ) ^ (logb 3 (10 : ℝ)) = (10 : ℝ) := by 
          rw [Real.rpow_logb]
          all_goals norm_num
        rw [h18, h19, h20, h21]
        all_goals norm_num
      rw [h14]
      exact h15
    rw [h12, h13]
    all_goals norm_num