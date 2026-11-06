import Mathlib

open Real

theorem algebra_188230 {x : ℝ} (hx : 0 < x) :
    (logb 10 (100 * x))^2 + (logb 10 (10 * x))^2 =
    14 + logb 10 (1 / x) ↔
    x = 10^(-9 / 2 : ℝ) ∨ x = 10 := by 
  constructor
  · -- Assume the equation holds, prove the solutions
    intro h_eq
    have h1 : logb 10 (100 * x) = 2 + logb 10 x := by
      calc
        logb 10 (100 * x) = logb 10 100 + logb 10 x := by rw [logb_mul (by norm_num) (by linarith)]
        _ = logb 10 (10 ^ (2 : ℝ)) + logb 10 x := by norm_num
        _ = (2 : ℝ) + logb 10 x := by 
          rw [logb_rpow (by norm_num)]
          all_goals norm_num
    have h2 : logb 10 (10 * x) = 1 + logb 10 x := by
      calc
        logb 10 (10 * x) = logb 10 10 + logb 10 x := by rw [logb_mul (by norm_num) (by linarith)]
        _ = (1 : ℝ) + logb 10 x := by 
          norm_num [logb_eq_iff_rpow_eq]
    have h3 : logb 10 (1 / x) = - logb 10 x := by 
      field_simp [logb_div, logb_one]
    rw [h1, h2, h3] at h_eq
    have h4 : 2 * (logb 10 x) ^ 2 + 7 * (logb 10 x) - 9 = 0 := by
      nlinarith 
    have h5 : (logb 10 x - 1) * (logb 10 x + 9 / 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h5) with h6 h7 
    · -- Case $\logb 10 x - 1 = 0$, so $\logb 10 x = 1$, so $x = 10$
      have h8 : logb 10 x = 1 := by linarith 
      have h9 : x = 10 := by 
        have h10 : x = (10 : ℝ) ^ (logb 10 x : ℝ) := by 
          field_simp 
        rw [h10, h8] 
        norm_num 
      right 
      exact h9 
    · -- Case $\logb 10 x + 9/2 = 0$, so $\logb 10 x = -9/2$, so $x = 10^{-9/2}$
      have h8 : logb 10 x = -9 / 2 := by linarith 
      have h9 : x = (10 : ℝ) ^ (-9 / 2 : ℝ) := by 
        have h10 : x = (10 : ℝ) ^ (logb 10 x : ℝ) := by 
          field_simp 
        rw [h10, h8] 
        all_goals norm_num 
      left 
      exact h9 
  · -- Show that the solutions satisfy the equation
    rintro (h_eq | h_eq)
    · -- Case $x = 10^{-9/2}$
      rw [h_eq] 
      have h1 : logb 10 (100 * (10 ^ (-9 / 2 : ℝ)) ) = 2 + logb 10 (10 ^ (-9 / 2 : ℝ)) := by 
        calc 
          logb 10 (100 * (10 ^ (-9 / 2 : ℝ)) ) = logb 10 100 + logb 10 (10 ^ (-9 / 2 : ℝ)) := by 
            rw [logb_mul (by norm_num) (by positivity)]
          _ = logb 10 (10 ^ (2 : ℝ)) + logb 10 (10 ^ (-9 / 2 : ℝ)) := by norm_num 
          _ = (2 : ℝ) + logb 10 (10 ^ (-9 / 2 : ℝ)) := by 
            rw [logb_rpow (by norm_num)]
            all_goals norm_num 
      have h2 : logb 10 (10 * (10 ^ (-9 / 2 : ℝ)) ) = 1 + logb 10 (10 ^ (-9 / 2 : ℝ)) := by 
        calc 
          logb 10 (10 * (10 ^ (-9 / 2 : ℝ)) ) = logb 10 10 + logb 10 (10 ^ (-9 / 2 : ℝ)) := by 
            rw [logb_mul (by norm_num) (by positivity)]
          _ = (1 : ℝ) + logb 10 (10 ^ (-9 / 2 : ℝ)) := by 
            norm_num [logb_eq_iff_rpow_eq]
      have h3 : logb 10 (1 / (10 ^ (-9 / 2 : ℝ)) ) = - logb 10 (10 ^ (-9 / 2 : ℝ)) := by 
        field_simp [logb_div, logb_one]
      have h4 : logb 10 (10 ^ (-9 / 2 : ℝ)) = (-9 / 2 : ℝ) := by 
        rw [logb_rpow]
        all_goals norm_num 
      rw [h1, h2, h3, h4] 
      norm_num 
    · -- Case $x = 10$
      rw [h_eq] 
      have h1 : logb 10 (100 * (10 : ℝ) ) = 3 := by 
        calc 
          logb 10 (100 * (10 : ℝ) ) = logb 10 1000 := by norm_num 
          _ = logb 10 (10 ^ (3 : ℝ)) := by norm_num 
          _ = (3 : ℝ) := by 
            rw [logb_rpow (by norm_num)]
            all_goals norm_num 
      have h2 : logb 10 (10 * (10 : ℝ) ) = 2 := by 
        calc 
          logb 10 (10 * (10 : ℝ) ) = logb 10 100 := by norm_num 
          _ = logb 10 (10 ^ (2 : ℝ)) := by norm_num 
          _ = (2 : ℝ) := by 
            rw [logb_rpow (by norm_num)]
            all_goals norm_num 
      have h3 : logb 10 (1 / (10 : ℝ) ) = -1 := by 
        have h4 : logb 10 (1 / 10) = logb 10 1 - logb 10 10 := by 
          field_simp [logb_div] 
        rw [h4] 
        norm_num [logb_one] 
      rw [h1, h2, h3] 
      all_goals norm_num 
      all_goals norm_num