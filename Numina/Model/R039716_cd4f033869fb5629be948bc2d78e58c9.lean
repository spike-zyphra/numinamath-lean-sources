import Mathlib

open Real

theorem inequalities_82721 (a : ℝ) (ha : 0 < a) (x : Fin 3 → ℝ)
    (hsum : ∑ i, x i = 0) :
    3 ≤ logb 2 (1 + a ^ x 0) + logb 2 (1 + a ^ x 1) + logb 2 (1 + a ^ x 2) := by
  have h1 : x 0 + x 1 + x 2 = 0 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum
    linarith

  have h2 : logb 2 (1 + a ^ x 0) + logb 2 (1 + a ^ x 1) + logb 2 (1 + a ^ x 2) =
      logb 2 ((1 + a ^ x 0) * (1 + a ^ x 1) * (1 + a ^ x 2)) := by
    have pos1 : 0 < (1 + a ^ x 0 : ℝ) := by positivity
    have pos2 : 0 < (1 + a ^ x 1 : ℝ) := by positivity
    have pos3 : 0 < (1 + a ^ x 2 : ℝ) := by positivity
    have eq7 : logb 2 (1 + a ^ x 0) + logb 2 (1 + a ^ x 1) + logb 2 (1 + a ^ x 2) =
        (logb 2 (1 + a ^ x 0) + logb 2 (1 + a ^ x 1)) + logb 2 (1 + a ^ x 2) := by ring
    have eq8 : logb 2 (1 + a ^ x 0) + logb 2 (1 + a ^ x 1) = logb 2 ((1 + a ^ x 0) * (1 + a ^ x 1)) := by
      rw [logb_mul (by positivity) (by positivity)]
    have eq9 : logb 2 ((1 + a ^ x 0) * (1 + a ^ x 1)) + logb 2 (1 + a ^ x 2) = logb 2 ((1 + a ^ x 0) * (1 + a ^ x 1) * (1 + a ^ x 2)) := by
      have pos1' : 0 < ((1 + a ^ x 0) * (1 + a ^ x 1) : ℝ) := by positivity
      have pos2' : 0 < (1 + a ^ x 2 : ℝ) := by positivity
      have h12 : logb 2 ((1 + a ^ x 0) * (1 + a ^ x 1)) + logb 2 (1 + a ^ x 2) = logb 2 (( (1 + a ^ x 0) * (1 + a ^ x 1) ) * (1 + a ^ x 2)) := by
        rw [← logb_mul (by positivity) (by positivity)]
      have h13 : ((1 + a ^ x 0) * (1 + a ^ x 1)) * (1 + a ^ x 2) = (1 + a ^ x 0) * (1 + a ^ x 1) * (1 + a ^ x 2) := by ring
      rw [h13] at h12
      linarith
    calc 
      logb 2 (1 + a ^ x 0) + logb 2 (1 + a ^ x 1) + logb 2 (1 + a ^ x 2) = (logb 2 (1 + a ^ x 0) + logb 2 (1 + a ^ x 1)) + logb 2 (1 + a ^ x 2) := by ring
      _ = logb 2 ((1 + a ^ x 0) * (1 + a ^ x 1)) + logb 2 (1 + a ^ x 2) := by
        rw [eq8]
      _ = logb 2 ((1 + a ^ x 0) * (1 + a ^ x 1) * (1 + a ^ x 2)) := by
        linarith [eq9]

  rw [h2]

  have h3 : (1 + a ^ x 0) * (1 + a ^ x 1) * (1 + a ^ x 2) ≥ (8 : ℝ) := by
    have h4 : a ^ x 0 > 0 := by positivity
    have h5 : a ^ x 1 > 0 := by positivity
    have h6 : a ^ x 2 > 0 := by positivity
    have h10 : a ^ x 0 * a ^ x 1 * a ^ x 2 = 1 := by
      have h13 : a ^ x 0 * a ^ x 1 * a ^ x 2 = a ^ (x 0 + x 1 + x 2) := by
        rw [← Real.rpow_add, ← Real.rpow_add]
        all_goals
          ring_nf
          <;> norm_num [ha]
          all_goals nlinarith
      rw [h13, h1]
      norm_num
    nlinarith [mul_pos (show 0 < a ^ x 0 by positivity) (show 0 < a ^ x 1 by positivity), 
        mul_pos (show 0 < a ^ x 0 by positivity) (show 0 < a ^ x 2 by positivity), 
        mul_pos (show 0 < a ^ x 1 by positivity) (show 0 < a ^ x 2 by positivity), 
        sq_nonneg (a ^ x 0 - 1), sq_nonneg (a ^ x 1 - 1), sq_nonneg (a ^ x 2 - 1), 
        sq_nonneg (a ^ x 0 - a ^ x 1), sq_nonneg (a ^ x 0 - a ^ x 2), sq_nonneg (a ^ x 1 - a ^ x 2), 
        h10]

  have h4 : logb 2 ((1 + a ^ x 0) * (1 + a ^ x 1) * (1 + a ^ x 2)) ≥ (3 : ℝ) := by
    have h6 : logb 2 ((1 + a ^ x 0) * (1 + a ^ x 1) * (1 + a ^ x 2)) ≥ logb 2 (8 : ℝ) := by 
      apply Real.logb_le_logb_of_le 
      all_goals
        nlinarith [h3, show (8 : ℝ) > 0 by norm_num, show (1 + a ^ x 0) * (1 + a ^ x 1) * (1 + a ^ x 2) > 0 by positivity]
    have h7 : logb 2 (8 : ℝ) = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith [h7, h6]
  linarith [h4]