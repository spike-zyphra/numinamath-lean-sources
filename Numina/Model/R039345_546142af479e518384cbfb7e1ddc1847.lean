import Mathlib

theorem algebra_10309 (t : ℝ) :
  3 * 3^t + Real.sqrt (9 * 9^t) = 18 ↔ t = 1 := by
  constructor
  · -- Forward direction: If the equation holds, then t = 1
    intro h
    have h1 : Real.sqrt (9 * (9 : ℝ) ^ t) = (3 : ℝ) ^ (1 + t : ℝ) := by
      have h2 : (9 * (9 : ℝ) ^ t : ℝ) = ((3 : ℝ) ^ (2 + 2 * t : ℝ)) := by
        calc
          (9 * (9 : ℝ) ^ t : ℝ) = (3 ^ (2 : ℝ) : ℝ) * ((3 ^ (2 : ℝ) : ℝ) ^ t) := by
            norm_num
          _ = (3 ^ (2 : ℝ) : ℝ) * (3 ^ (2 * t : ℝ) : ℝ) := by
            rw [← Real.rpow_mul]
            ring_nf
            all_goals norm_num
          _ = (3 : ℝ) ^ (2 + 2 * t : ℝ) := by
            rw [← Real.rpow_add]
            ring_nf
            all_goals norm_num
      rw [h2]
      have h3 : Real.sqrt ((3 : ℝ) ^ (2 + 2 * t : ℝ)) = (3 : ℝ) ^ (1 + t : ℝ) := by
        have h4 : Real.sqrt ((3 : ℝ) ^ (2 + 2 * t : ℝ)) = ((3 : ℝ) ^ (1 + t : ℝ)) := by
          have h5 : ((3 : ℝ) ^ (1 + t : ℝ)) ^ 2 = (3 : ℝ) ^ (2 + 2 * t : ℝ) := by
            calc
              ((3 : ℝ) ^ (1 + t : ℝ)) ^ 2
                = (3 : ℝ) ^ (2 * (1 + t : ℝ) : ℝ) := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul]
                  ring_nf
                  all_goals norm_num
              _ = (3 : ℝ) ^ (2 + 2 * t : ℝ) := by
                ring_nf
          have h6 : 0 ≤ (3 : ℝ) ^ (1 + t : ℝ) := by positivity
          rw [← h5]
          field_simp [Real.sqrt_sq (show 0 ≤ (3 : ℝ) ^ (1 + t : ℝ) by positivity)]
        linarith
      linarith
    rw [h1] at h
    have h2 : (3 : ℝ) ^ (1 + t : ℝ) = 3 * (3 : ℝ) ^ t := by
      rw [Real.rpow_add]
      ring_nf
      all_goals norm_num
    rw [h2] at h
    have h3 : (3 : ℝ) ^ t = 3 := by
      have h4 : (3 : ℝ) ^ t > 0 := by positivity
      nlinarith [show (0 : ℝ) ≤ (3 : ℝ) ^ t by positivity, show (3 : ℝ) ^ t > (0 : ℝ) by positivity, Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) t]
    have h4 : t = (1 : ℝ) := by
      apply_fun (Real.logb (3 : ℝ)) at h3
      have h5 : Real.logb (3 : ℝ) ((3 : ℝ) ^ t) = t := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h6 : Real.logb (3 : ℝ) (3 : ℝ) = 1 := by
        norm_num [Real.logb_self_eq_one]
      rw [h5, h6] at h3
      linarith
    linarith
  · -- Backward direction: If t = 1, then the equation holds
    intro h
    rw [h]
    have h1 : Real.sqrt (9 * (9 : ℝ) ^ (1 : ℝ)) = (3 : ℝ) ^ (1 + (1 : ℝ) : ℝ) := by
      have h2 : (9 * (9 : ℝ) ^ (1 : ℝ) : ℝ) = ((3 : ℝ) ^ (2 + 2 * (1 : ℝ) : ℝ)) := by
        norm_num
        <;> norm_num
      rw [h2]
      have h3 : Real.sqrt ((3 : ℝ) ^ (2 + 2 * (1 : ℝ) : ℝ)) = (3 : ℝ) ^ (1 + (1 : ℝ) : ℝ) := by
        have h4 : Real.sqrt ((3 : ℝ) ^ (2 + 2 * (1 : ℝ) : ℝ)) = (3 : ℝ) ^ (1 + (1 : ℝ) : ℝ) := by
          have h5 : ((3 : ℝ) ^ (1 + (1 : ℝ) : ℝ)) ^ 2 = (3 : ℝ) ^ (2 + 2 * (1 : ℝ) : ℝ) := by
            calc
              ((3 : ℝ) ^ (1 + (1 : ℝ) : ℝ)) ^ 2
                = (3 : ℝ) ^ (2 * (1 + (1 : ℝ) : ℝ) : ℝ) := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul]
                  ring_nf
                  all_goals norm_num
              _ = (3 : ℝ) ^ (2 + 2 * (1 : ℝ) : ℝ) := by
                ring_nf
          have h6 : 0 ≤ (3 : ℝ) ^ (1 + (1 : ℝ) : ℝ) := by positivity
          rw [← h5]
          field_simp [Real.sqrt_sq (show 0 ≤ (3 : ℝ) ^ (1 + (1 : ℝ) : ℝ) by positivity)]
        linarith
      linarith
    have h2 : (3 : ℝ) ^ (1 + (1 : ℝ) : ℝ) = 3 * (3 : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_add]
      ring_nf
      all_goals norm_num
    nlinarith [h1, h2, Real.sqrt_nonneg (9 * (9 : ℝ) ^ (1 : ℝ)), Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) (1 + (1 : ℝ)), Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) (1 : ℝ)]