import Mathlib

open Real Set

theorem calculus_11186 {x : ℝ} (n : ℝ) (hn : n > 0) (sinpos : 0 < sin x) (cospos : 0 < cos x)
  (h1 : logb 10 (sin x) + logb 10 (cos x) = -1) :
  logb 10 (sin x + cos x) = (logb 10 n - 1) / 2 ↔ n = 12 := by
  constructor
  · -- Forward: equation to n=12
    intro h
    have h2 : sin x * cos x = 1 / 10 := by
      have h3 : logb 10 (sin x * cos x) = -1 := by
        rw [logb_mul (by linarith) (by linarith)]
        linarith
      have h4 : sin x * cos x = (10 : ℝ) ^ (-1 : ℝ) := by 
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by nlinarith [sinpos, cospos] ) ] at h3
        · linarith
        all_goals nlinarith
      rw [h4]
      all_goals norm_num
    have h3 : (sin x + cos x) ^ 2 = 6 / 5 := by
      have h4 : (sin x + cos x) ^ 2 = (sin x) ^ 2 + (cos x) ^ 2 + 2 * (sin x * cos x) := by
        ring
      rw [h4]
      have h5 : (sin x) ^ 2 + (cos x) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq x
      rw [h5, h2]
      all_goals norm_num
    have h4 : logb 10 ((sin x + cos x) ^ 2) = logb 10 n - 1 := by
      have h5 : logb 10 ((sin x + cos x) ^ 2) = 2 * logb 10 (sin x + cos x) := by
        simp [logb_pow]
      have h6 : 2 * logb 10 (sin x + cos x) = logb 10 n - 1 := by
        linarith [h]
      linarith [h5, h6]
    have h5 : logb 10 ((sin x + cos x) ^ 2) = logb 10 (n / 10) := by
      have h6 : logb 10 (n / 10) = logb 10 n - logb 10 10 := by
        rw [logb_div (by linarith) (by norm_num)]
      have h7 : logb 10 10 = 1 := by
        norm_num [logb_self_eq_one]
      rw [h6, h7]
      all_goals linarith
    -- From h5 : logarithm equal => arguments equal
    have h13 : (sin x + cos x) ^ 2 > 0 := by 
      nlinarith [sinpos, cospos, h2]
    have h14 : n / 10 > 0 := by
      apply div_pos
      linarith
      norm_num
    have h15 : (sin x + cos x) ^ 2 = n / 10 := by
      have h16 : (sin x + cos x) ^ 2 > 0 := h13
      have h17 : n / 10 > 0 := h14
      have h18 : logb 10 ((sin x + cos x) ^ 2) = logb 10 (n / 10) := by
        linarith [h4, h5]
      -- Use injectivity of logarithm on positive numbers
      have h19 : (sin x + cos x) ^ 2 = n / 10 := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h16) (Set.mem_Ioi.mpr h17) h18
      exact h19
    rw [h3] at h15
    have h16 : n = 12 := by
      field_simp at h15
      nlinarith
    linarith
  · -- Backward: n=12 to equation
    intro h_eq
    rw [show n = 12 by linarith [h_eq]]
    have h3 : (sin x + cos x) ^ 2 = 6 / 5 := by
      have h4 : (sin x + cos x) ^ 2 = (sin x) ^ 2 + (cos x) ^ 2 + 2 * (sin x * cos x) := by
        ring
      rw [h4]
      have h5 : (sin x) ^ 2 + (cos x) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq x
      have h2 : sin x * cos x = 1 / 10 := by
        have h3 : logb 10 (sin x * cos x) = -1 := by
          rw [logb_mul (by linarith) (by linarith)]
          linarith
        have h4 : sin x * cos x = (10 : ℝ) ^ (-1 : ℝ) := by 
          rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by nlinarith [sinpos, cospos] ) ] at h3
          · linarith
          all_goals nlinarith
        rw [h4]
        all_goals norm_num
      rw [h5, h2]
      all_goals norm_num
    -- Compute logarithm
    have h6 : logb 10 ((sin x + cos x)^2) = logb 10 (6 / 5) := by
      have h7 : (sin x + cos x)^2 = 6 / 5 := h3
      rw [h7]
    have h7 : logb 10 ((sin x + cos x)^2) = 2 * logb 10 (sin x + cos x) := by
      simp [logb_pow]
    -- Goal is `logb 10 (sin x + cos x) = (logb 10 12 - 1) / 2`
    -- From above facts
    have h10 : logb 10 (6 / 5) = logb 10 12 - 1 := by
      have h10 : logb 10 (6 / 5) = logb 10 6 - logb 10 5 := by
        rw [logb_div (by norm_num) (by norm_num)]
      have h11 : logb 10 6 = logb 10 12 - logb 10 2 := by
        have h12 : logb 10 12 = logb 10 (6 * 2) := by
          norm_num
        have h13 : logb 10 (6 * 2) = logb 10 6 + logb 10 2 := by
          rw [logb_mul (by norm_num) (by norm_num)]
        linarith [h12, h13]
      have h14 : logb 10 6 - logb 10 5 = (logb 10 12 - logb 10 2) - logb 10 5 := by 
        rw [h11]
      have h15 : (logb 10 12 - logb 10 2) - logb 10 5 = logb 10 12 - (logb 10 2 + logb 10 5) := by 
        ring
      have h16 : logb 10 2 + logb 10 5 = 1 := by 
        have h17 : logb 10 2 + logb 10 5 = logb 10 (2 * 5) := by 
          rw [logb_mul (by norm_num) (by norm_num)]
        have h18 : logb 10 (2 * 5) = logb 10 10 := by 
          norm_num
        have h19 : logb 10 10 = 1 := by 
          norm_num [logb_self_eq_one]
        linarith [h17, h18, h19]
      have h17 : logb 10 (6 / 5) = logb 10 12 - 1 := by 
        linarith [h10, h16]
      linarith
    -- Combine facts
    have h11 : 2 * logb 10 (sin x + cos x) = logb 10 12 - 1 := by 
      linarith [h6, h7, h10]
    linarith