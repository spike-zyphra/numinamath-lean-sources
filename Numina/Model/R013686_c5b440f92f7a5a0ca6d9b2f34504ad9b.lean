import Mathlib

open Real

theorem algebra_9549 {x : ℝ} (hx : 0 < x) :
    logb 7 (x^2 + 72) + logb 7 49 - 2 * logb 7 x = 3 ↔
    x = 2 * sqrt 3 := by
  constructor
  · -- Forward: if the equation holds, then x = 2*sqrt(3)
    intro h
    have h1 : logb 7 (x^2 + 72) + logb 7 49 - 2 * logb 7 x = 3 := by linarith
    have h2 : logb 7 (x^2 + 72) + logb 7 49 = 2 * logb 7 x + 3 := by
      linarith
    have h3 : 2 * logb 7 x = logb 7 (x ^ 2) := by
      simp [logb_pow]
    have h4 : logb 7 (x^2 + 72) + logb 7 49 = logb 7 ((x^2 + 72) * 49) := by
      rw [logb_mul (by positivity) (by positivity)]
    rw [h4] at h2
    rw [h3] at h2
    have h5 : logb 7 (x ^ 2) + 3 = logb 7 (x ^ 2 * (7 ^ 3 : ℝ)) := by
      have h6 : logb 7 (x ^ 2 * (7 ^ 3 : ℝ)) = logb 7 (x ^ 2) + logb 7 ((7 ^ 3 : ℝ)) := by
        rw [logb_mul (by positivity) (by positivity)]
      have h7 : logb 7 ((7 ^ 3 : ℝ)) = (3 : ℝ) := by
        calc
          logb 7 ((7 ^ 3 : ℝ)) = 3 * logb 7 (7 : ℝ) := by simp [logb_pow]
          _ = 3 * (1 : ℝ) := by
            rw [logb_self_eq_one]
            all_goals norm_num
          _ = (3 : ℝ) := by norm_num
      rw [h6, h7]
    have h8 : (x ^ 2 + 72) * 49 = x ^ 2 * (7 ^ 3 : ℝ) := by
      have h9 : logb 7 ((x^2 + 72) * 49) = logb 7 (x ^ 2 * (7 ^ 3 : ℝ)) := by
        linarith [h2, h5]
      have h10 : (x^2 + 72) * 49 > 0 := by positivity
      have h11 : x ^ 2 * (7 ^ 3 : ℝ) > 0 := by positivity
      have h12 : (x ^ 2 + 72) * 49 = x ^ 2 * (7 ^ 3 : ℝ) := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h10) (Set.mem_Ioi.mpr h11) h9
      exact h12
    have h9 : (7 ^ 3 : ℝ) = 343 := by norm_num
    rw [h9] at h8
    have h10 : x ^ 2 = 12 := by
      nlinarith
    have h11 : x = Real.sqrt 12 := by
      have h12 : x > 0 := by linarith
      have h13 : x ^ 2 = 12 := h10
      have h14 : x = Real.sqrt 12 := by
        rw [← h13]
        field_simp
      exact h14
    have h12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
      calc
        Real.sqrt 12 = Real.sqrt (2 ^ 2 * 3) := by norm_num
        _ = (Real.sqrt (2 ^ 2)) * (Real.sqrt (3)) := by rw [Real.sqrt_mul (by norm_num)]
        _ = (2) * (Real.sqrt 3) := by
          rw [show Real.sqrt (2 ^ 2) = (2 : ℝ) by
            rw [Real.sqrt_sq (by norm_num)]
          ]
        _ = (2 * Real.sqrt 3) := by ring
    rw [h12] at h11
    linarith
  · -- Backward: if x = 2*sqrt(3), then the equation holds
    intro h
    rw [h]
    have h1 : Real.sqrt 3 ^ 2 = 3 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h2 : (2 * Real.sqrt 3) ^ 2 = 12 := by
      calc
        (2 * Real.sqrt 3) ^ 2 = 4 * (Real.sqrt 3 ^ 2) := by ring
        _ = 4 * 3 := by rw [h1]
        _ = (12 : ℝ) := by norm_num
    have h3 : logb 7 ((2 * Real.sqrt 3) ^ 2 + 72) = logb 7 84 := by
      have h4 : (2 * Real.sqrt 3) ^ 2 + 72 = (84 : ℝ) := by
        nlinarith [h2]
      rw [h4]
    have h4 : 2 * logb 7 (2 * Real.sqrt 3) = logb 7 12 := by
      have h5 : 2 * logb 7 (2 * Real.sqrt 3) = logb 7 ((2 * Real.sqrt 3) ^ 2) := by
        simp [logb_pow]
      rw [h5]
      have h6 : (2 * Real.sqrt 3) ^ 2 = (12 : ℝ) := h2
      rw [h6]
    have h7 : logb 7 84 + logb 7 49 - 2 * logb 7 (2 * Real.sqrt 3) = 3 := by
      rw [show 2 * logb 7 (2 * Real.sqrt 3) = logb 7 12 by linarith [h4]]
      have h8 : logb 7 84 + logb 7 49 - logb 7 12 = 3 := by
        have h9 : logb 7 84 + logb 7 49 = logb 7 (84 * 49) := by
          rw [logb_mul (by positivity) (by positivity)]
        have h10 : logb 7 (84 * 49) - logb 7 12 = logb 7 ((84 * 49) / (12 : ℝ)) := by
          rw [← logb_div (by positivity) (by positivity)]
        have h11 : logb 7 ((84 * 49) / (12 : ℝ)) = logb 7 (343 : ℝ) := by
          have h12 : (84 * 49 : ℝ) / (12 : ℝ) = (343 : ℝ) := by
            norm_num
          rw [h12]
        have h13 : logb 7 (343 : ℝ) = 3 := by
          rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)]
          all_goals norm_num
        calc
          logb 7 84 + logb 7 49 - logb 7 12 = (logb 7 84 + logb 7 49) - logb 7 12 := by ring
          _ = logb 7 (84 * 49) - logb 7 12 := by
            rw [h9]
          _ = logb 7 ((84 * 49) / (12 : ℝ)) := by
            rw [h10]
          _ = logb 7 (343 : ℝ) := by
            rw [h11]
          _ = (3 : ℝ) := by
            linarith [h13]
      linarith
    linarith [h3, h7]