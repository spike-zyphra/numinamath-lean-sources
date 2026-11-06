import Mathlib

open Real

theorem inequalities_171236 (x : ℝ) (h : 4 * x + 5 > 0) (hx : sqrt (4 * x + 5) - 1 > 0) :
    logb 2 (sqrt (4 * x + 5) - 1) / logb 2 (sqrt (4 * x + 5) + 11) > 1 / 2 ↔ x > 5 := by
  constructor
  · -- Forward implication: If the inequality holds, then x > 5
    intro h1
    have h2 : sqrt (4 * x + 5) - 1 > 0 := hx
    have h3 : sqrt (4 * x + 5) > 1 := by linarith
    have h4 : sqrt (4 * x + 5) + 11 > 1 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 4 * x + 5 by linarith)]
    have h5 : logb 2 (sqrt (4 * x + 5) + 11) > 0 := by
      have h6 : sqrt (4 * x + 5) + 11 > 1 := h4
      have h7 : logb 2 (sqrt (4 * x + 5) + 11) > 0 := by
        apply logb_pos
        all_goals nlinarith
      linarith
    have h7 : logb 2 (sqrt (4 * x + 5) - 1) / logb 2 (sqrt (4 * x + 5) + 11) > 1 / 2 := h1
    have h8 : 2 * logb 2 (sqrt (4 * x + 5) - 1) > logb 2 (sqrt (4 * x + 5) + 11) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mp at h7
      linarith
    -- Now convert to polynomial inequality.
    have h9 : 2 * logb 2 (sqrt (4 * x + 5) - 1) = logb 2 ((sqrt (4 * x + 5) - 1) ^ 2) := by
      simp [logb_pow]
    have h10 : logb 2 ((sqrt (4 * x + 5) - 1) ^ 2) > logb 2 (sqrt (4 * x + 5) + 11) := by
      linarith [h8, h9]
    have h11 : (sqrt (4 * x + 5) - 1) ^ 2 > sqrt (4 * x + 5) + 11 := by
      apply (logb_lt_logb_iff (by norm_num) (by nlinarith) (by nlinarith)).mp at h10
      all_goals
        nlinarith
    -- Now solve quadratic.
    have h12 : sqrt (4 * x + 5) > 5 := by
      nlinarith [Real.sqrt_nonneg (4 * x + 5), Real.sq_sqrt (show 0 ≤ (4 * x + 5 : ℝ) by nlinarith)]
    have h13 : 4 * x + 5 > 25 := by
      nlinarith [Real.sqrt_nonneg (4 * x + 5), Real.sq_sqrt (show 0 ≤ (4 * x + 5 : ℝ) by nlinarith), h12]
    linarith
  · -- Backward implication: If x > 5, then the inequality holds
    intro h2
    have h4 : sqrt (4 * x + 5) + 11 > 1 := by
      have h5 : sqrt (4 * x + 5) > 1 := by
        have h1 : 4 * x + 5 > 5 := by linarith
        have h2 : sqrt (4 * x + 5) > sqrt (5 : ℝ) := by
          apply Real.sqrt_lt_sqrt
          all_goals linarith
        have h3 : sqrt (5 : ℝ) > 1 := by
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
        linarith
      nlinarith [Real.sqrt_nonneg (4 * x + 5), Real.sq_sqrt (show 0 ≤ (4 * x + 5 : ℝ) by nlinarith)]
    have h5 : logb 2 (sqrt (4 * x + 5) + 11) > 0 := by
      have h6 : sqrt (4 * x + 5) + 11 > 1 := h4
      have h7 : logb 2 (sqrt (4 * x + 5) + 11) > 0 := by
        apply logb_pos
        all_goals nlinarith
      linarith
    -- We need that exponentiation gives relevant inequality.
    have h7 : sqrt (4 * x + 5) > 5 := by
      nlinarith [Real.sqrt_nonneg (4 * x + 5), Real.sq_sqrt (show 0 ≤ (4 * x + 5 : ℝ) by nlinarith)]
    have h8 : (sqrt (4 * x + 5) - 1) ^ 2 > sqrt (4 * x + 5) + 11 := by
      nlinarith [Real.sqrt_nonneg (4 * x + 5), Real.sq_sqrt (show 0 ≤ (4 * x + 5: ℝ) by nlinarith), h7]
    -- Now establish the implication.
    have h9 : logb 2 ((sqrt (4 * x + 5) - 1) ^ 2) > logb 2 (sqrt (4 * x + 5) + 11) := by
      apply (logb_lt_logb_iff (by norm_num) (by nlinarith) (by nlinarith)).mpr
      all_goals
        nlinarith
    have h10 : 2 * logb 2 (sqrt (4 * x + 5) - 1) > logb 2 (sqrt (4 * x + 5) + 11) := by
      have h11 : logb 2 ((sqrt (4 * x + 5) - 1) ^ 2) = 2 * logb 2 (sqrt (4 * x + 5) - 1) := by
        simp [logb_pow]
      linarith [h9, h11]
    -- Now form the division inequalities conclude this direction.
    have h11 : logb 2 (sqrt (4 * x + 5) - 1) / logb 2 (sqrt (4 * x + 5) + 11) > 1 / 2 := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      linarith
    linarith [h11]