import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_258180 (x : ℝ) :
  (sqrt (sin x ^ 2 + 2) + 2 ^ x) / (sqrt (sin x ^ 2 + 2) + 2 ^ (x + 1)) +
  (sqrt (logb 10 x ^ 2 + 3) + 3 ^ x) / (sqrt (logb 10 x ^ 2 + 3) + 3 ^ (x + 1)) +
  (sqrt (exp x + 6) + 6 ^ x) / (sqrt (exp x + 6) + 6 ^ (x + 1)) ≠ 1 := by 
  intro h
  have h1 : (sqrt (sin x ^ 2 + 2) + (2:ℝ) ^ x) / (sqrt (sin x ^ 2 + 2) + (2:ℝ) ^ (x + 1)) > 1 / 2 := by
    have h30 : sqrt (sin x ^ 2 + 2) > 0 := by
      have h4 : sin x ^ 2 + 2 > 0 := by 
        nlinarith [sq_nonneg (sin x), Real.sin_sq_add_cos_sq x]
      have h5 : sqrt (sin x ^ 2 + 2) > 0 := by 
        apply Real.sqrt_pos.mpr 
        linarith [h4]
      linarith [h5]
    have h50 : (2:ℝ) ^ (x + 1) = (2:ℝ) ^x * 2 := by
      rw [Real.rpow_add]
      ring
      all_goals norm_num
    have h60 : sqrt (sin x ^ 2 + 2) + (2:ℝ) ^ (x + 1) > 0 := by 
      have h40 : sqrt (sin x ^ 2 + 2) > 0 := h30 
      have h90 : (2:ℝ) ^ (x + 1) > 0 := by
        rw [h50]
        positivity
      linarith 
    apply (lt_div_iff₀ (by positivity)).mpr
    rw [h50]
    nlinarith [Real.sqrt_nonneg (sin x ^ 2 + 2), sq_nonneg ((2:ℝ) ^x), Real.sq_sqrt (show 0 ≤ (sin x ^ 2 + 2 : ℝ) by positivity), show 0 ≤ (2:ℝ) ^x by positivity]
  have h2 : (sqrt (logb 10 x ^ 2 + 3) + (3:ℝ) ^ x) / (sqrt (logb 10 x ^ 2 + 3) + (3:ℝ) ^ (x + 1)) > 1 / 3 := by 
    have h30 : sqrt (logb 10 x ^ 2 + 3) > 0 := by
      have h4 : logb 10 x ^ 2 + 3 > 0 := by 
        nlinarith [sq_nonneg (logb 10 x), Real.sin_sq_add_cos_sq x]
      have h5 : sqrt (logb 10 x ^ 2 + 3) > 0 := by 
        apply Real.sqrt_pos.mpr
        linarith [h4]
      linarith [h5]
    have h51 : (3:ℝ) ^ (x + 1) = (3:ℝ) ^x * 3 := by
      rw [Real.rpow_add]
      ring
      all_goals norm_num 
    have h7 : sqrt (logb 10 x ^ 2 + 3) + (3:ℝ) ^ (x + 1) > 0 := by 
      have h8 : sqrt (logb 10 x ^ 2 + 3) > 0 := h30 
      have h9 : (3:ℝ) ^ (x + 1) > 0 := by
        rw [h51]
        positivity 
      linarith 
    apply (lt_div_iff₀ (by positivity)).mpr
    rw [h51]
    nlinarith [Real.sqrt_nonneg (logb 10 x ^ 2 + 3), sq_nonneg ((3:ℝ) ^x), Real.sq_sqrt (show 0 ≤ (logb 10 x ^ 2 + 3 : ℝ) by positivity), show 0 ≤ (3:ℝ) ^x by positivity]
  have h3 : (sqrt (exp x + 6) + (6:ℝ) ^ x) / (sqrt (exp x + 6) + (6:ℝ) ^ (x + 1)) > 1 / 6 := by
    have h30 : sqrt (exp x + 6) > 0 := by 
      have h4 : exp x + 6 > 0 := by
        have h0 : exp x > 0 := Real.exp_pos x 
        linarith 
      have h5 : sqrt (exp x + 6) > 0 := by 
        apply Real.sqrt_pos.mpr
        linarith 
      linarith 
    have h52 : (6:ℝ) ^ (x + 1) = (6:ℝ) ^x * 6 := by 
      rw [Real.rpow_add]
      ring 
      all_goals norm_num 
    have  h7 : sqrt (exp x + 6) + (6:ℝ) ^ (x + 1) > 0 := by 
      have h5 : sqrt (exp x + 6) > 0 := h30 
      have h6 : (6:ℝ) ^ (x + 1) > 0 := by
        rw [h52]
        positivity 
      linarith 
    apply (lt_div_iff₀ (by positivity)).mpr
    rw [h52]
    nlinarith [Real.sqrt_nonneg (exp x + 6), sq_nonneg ((6:ℝ) ^x), Real.sq_sqrt (show 0 ≤ (exp x + 6 : ℝ) by positivity), show 0 ≤ (6:ℝ) ^x by positivity]
  linarith [h, h1, h2, h3]