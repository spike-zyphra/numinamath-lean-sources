import Mathlib

open Real

theorem algebra_187713 {x : ℝ} (hx : x > 0) :
    x * (logb 10 5 - 1) = logb 10 (2 ^ x + 1) - logb 10 6 ↔ x = 1 := by
  constructor
  · -- Forward direction: If the equation holds, then x = 1
    intro h_eq
    have h1 : logb 10 5 = 1 - logb 10 2 := by
      calc
        logb 10 5 = logb 10 (10 / 2) := by norm_num
        _ = logb 10 10 - logb 10 2 := by rw [logb_div (by norm_num) (by norm_num)]
        _ = 1 - logb 10 2 := by simp
    have eq1 : x * (logb 10 5 - 1) = -x * (logb 10 2) := by
      rw [show logb 10 5 = 1 - logb 10 2 by linarith [h1]]
      all_goals ring
    have eq2 : logb 10 (2 ^ x + 1) - logb 10 6 = logb 10 ((2 ^ x + 1) / 6) := by
      rw [← logb_div (by positivity) (by positivity)]
    rw [eq1, eq2] at h_eq
    have eq3 : -x * (logb 10 2) = logb 10 ((2 : ℝ) ^ (-x : ℝ)) := by
      have h4 : logb 10 ((2 : ℝ) ^ (-x : ℝ)) = -x * logb 10 (2 : ℝ) := by
        rw [logb_rpow_eq_mul_logb_of_pos]
        all_goals norm_num
      linarith
    rw [eq3] at h_eq
    have eq4 : (2 : ℝ) ^ (-x : ℝ) = (2 ^ x + 1) / 6 := by
      have h5 : (2 : ℝ) ^ (-x : ℝ) > 0 := by positivity
      have h6 : (2 ^ x + 1 : ℝ) / 6 > 0 := by
        have h7 : (2 : ℝ) ^ x > 0 := by positivity
        positivity
      have h8 : (2 : ℝ) ^ (-x : ℝ) = (2 ^ x + 1) / 6 := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h5) (Set.mem_Ioi.mpr h6) h_eq
      linarith
    have eq5 : (2 : ℝ) ^ (-x : ℝ) = (2 ^ x + 1) / 6 := eq4
    have eq6 : (2 : ℝ) ^ x > 0 := by positivity
    have eq7 : 6 * ((2 : ℝ) ^ (-x : ℝ)) = (2 : ℝ) ^ x + 1 := by
      have h12 : (2 : ℝ) ^ (-x : ℝ) = (2 ^ x + 1) / 6 := eq4
      field_simp at h12 ⊢
      linarith
    have eq9 : (2 : ℝ) ^ (-x : ℝ) = 1 / ((2 : ℝ) ^ x) := by
      rw [show (2 : ℝ) ^ (-x : ℝ) = ((2 : ℝ) ^ x)⁻¹ by rw [← Real.rpow_neg]; ring_nf; all_goals norm_num]
      field_simp
    rw [eq9] at eq7
    have eq11 : 6 = ((2 : ℝ) ^ x)^2 + (2 : ℝ) ^ x := by
      have eq12 : 6 * (1 / ((2 : ℝ) ^ x)) = (2 : ℝ) ^ x + 1 := by linarith
      have eq13 : (6 * (1 / ((2 : ℝ) ^ x))) * ((2 : ℝ) ^ x) = ((2 : ℝ) ^ x + 1) * ((2 : ℝ) ^ x) := by
        rw [eq12]
      have eq14 : (6 * (1 / ((2 : ℝ) ^ x))) * ((2 : ℝ) ^ x) = 6 := by
        field_simp [show (2 : ℝ) ^ x ≠ 0 by positivity]
      rw [eq14] at eq13
      have eq15 : ((2 : ℝ) ^ x + 1) * ((2 : ℝ) ^ x) = ((2 : ℝ) ^ x)^2 + (2 : ℝ) ^ x := by
        ring
      rw [eq15] at eq13
      linarith
    have eq12 : ((2 : ℝ) ^ x)^2 + (2 : ℝ) ^ x - 6 = 0 := by
      linarith
    have eq13 : ((2 : ℝ) ^ x + 3) * ((2 : ℝ) ^ x - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 eq13) with h10 h11
    ·
      have h14 : (2 : ℝ) ^ x + 3 = 0 := by linarith
      have h15 : (2 : ℝ) ^ x > 0 := by positivity
      linarith
    ·
      have h16 : (2 : ℝ) ^ x - 2 = 0 := by linarith
      have h17 : (2 : ℝ) ^ x = (2 : ℝ) := by
        linarith
      have h18 : x = 1 := by
        have h19 : (2 : ℝ) ^ x = (2 : ℝ) ^ (1 : ℝ) := by
          rw [h17]
          norm_num
        have h20 : x = (1 : ℝ) := by
          apply_fun (Real.logb (2 : ℝ)) at h19
          have h21 : Real.logb (2 : ℝ) ((2 : ℝ) ^ x) = x := by
            rw [Real.logb_rpow]
            all_goals norm_num
          have h22 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (1 : ℝ)) = (1 : ℝ) := by
            rw [Real.logb_rpow]
            all_goals norm_num
          linarith
        linarith
      linarith
  · -- Backward direction: If x = 1, then the equation holds
    intro h_eq
    rw [show x = 1 by linarith [h_eq]]
    have h1 : logb 10 5 = 1 - logb 10 2 := by
      calc
        logb 10 5 = logb 10 (10 / 2) := by norm_num
        _ = logb 10 10 - logb 10 2 := by rw [logb_div (by norm_num) (by norm_num)]
        _ = 1 - logb 10 2 := by simp
    have eq1 : (1 : ℝ) * (logb 10 5 - 1) = logb 10 (2 ^ (1 : ℝ) + 1) - logb 10 6 := by
      have eq2 : logb 10 (2 ^ (1 : ℝ) + 1) = logb 10 (3 : ℝ) := by
        norm_num
      rw [eq2]
      have eq3 : logb 10 5 = 1 - logb 10 2 := by
        linarith [h1]
      have eq4 : logb 10 6 = logb 10 2 + logb 10 3 := by
        calc
          logb 10 6 = logb 10 (2 * 3) := by norm_num
          _ = logb 10 2 + logb 10 3 := by rw [logb_mul (by norm_num) (by norm_num)]
      linarith [eq3, eq4]
    norm_num at eq1 ⊢
    all_goals linarith