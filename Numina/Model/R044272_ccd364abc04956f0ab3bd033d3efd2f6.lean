import Mathlib

theorem algebra_274065 {x : ℝ} {n : ℕ} (hn : n ≠ 0) (x_def : x = (1991 ^ ((1 : ℝ) / n) - 1991 ^ (-(1 : ℝ) / n)) / 2) :
    (x - Real.sqrt (1 + x ^ 2)) ^ n = (-1) ^ n / 1991 := by

  have h1 : x - Real.sqrt (1 + x ^ 2) = - (1991 : ℝ) ^ (-(1 : ℝ) / n) := by
    have h2 : Real.sqrt (1 + x ^ 2) = (1991 ^ ((1 : ℝ) / n) + 1991 ^ (-(1 : ℝ) / n)) / 2 := by
      have h3 : 1 + x^2 = ((1991 ^ ((1 : ℝ) / n) + 1991 ^ (-(1 : ℝ) / n)) / 2) ^ 2 := by
        rw [x_def]
        have h5 : ((1991 : ℝ) ^ ((1 : ℝ) / n)) * ((1991 : ℝ) ^ (-(1 : ℝ) / n)) = 1 := by
          have h7 : ((1991 : ℝ) ^ ((1 : ℝ) / n)) * ((1991 : ℝ) ^ (-(1 : ℝ) / n)) = (1991 : ℝ) ^ (0 : ℝ) := by
            rw [← Real.rpow_add]
            have h8 : (1 : ℝ) / n + (-(1 : ℝ) / n) = (0 : ℝ) := by ring
            rw [h8]
            all_goals
              positivity
          rw [h7]
          norm_num
        nlinarith [sq_nonneg ((1991 : ℝ) ^ ((1 : ℝ) / n) - (1991 : ℝ) ^ (-(1 : ℝ) / n)), sq_nonneg ((1991 : ℝ) ^ ((1 : ℝ) / n) + (1991 : ℝ) ^ (-(1 : ℝ) / n)), Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1991) (1 / n : ℝ), Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1991) (-1 / n : ℝ)]
      have h4 : Real.sqrt (1 + x ^ 2) = Real.sqrt (((1991 ^ ((1 : ℝ) / n) + 1991 ^ (-(1 : ℝ) / n)) / 2) ^ 2) := by 
        rw [h3]
      rw [h4]
      have h8 : Real.sqrt (((1991 ^ ((1 : ℝ) / n) + 1991 ^ (-(1 : ℝ) / n)) / 2) ^ 2) = (1991 ^ ((1 : ℝ) / n) + 1991 ^ (-(1 : ℝ) / n)) / 2 := by
        rw [Real.sqrt_sq (show 0 ≤ (1991 ^ ((1 : ℝ) / n) + 1991 ^ (-(1 : ℝ) / n)) / 2 by
          have h1 : 0 < (1991 : ℝ) ^ ((1 : ℝ) / n) := by positivity
          have h2 : 0 < (1991 : ℝ) ^ (-(1 : ℝ) / n) := by positivity
          positivity
        )]
      linarith
    rw [h2, x_def]
    have h7 : 0 < (1991 : ℝ) ^ ((1 : ℝ) / n) := by positivity
    have h8 : 0 < (1991 : ℝ) ^ (-(1 : ℝ) / n) := by positivity
    ring

  have h2 : (x - Real.sqrt (1 + x ^ 2)) ^ n = (-1 : ℝ) ^ n * ((1991 : ℝ) ^ (-(1 : ℝ) / n)) ^ n := by
    rw [h1]
    ring_nf

  have h3 : ((1991 : ℝ) ^ (-(1 : ℝ) / n)) ^ n = (1991 : ℝ) ^ (-1 : ℝ) := by
    have h4 : ((1991 : ℝ) ^ (-(1 : ℝ) / n)) ^ n = (1991 : ℝ) ^ (-(1 : ℝ) / n * (↑n : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals
        positivity
    have h5 : -(1 : ℝ) / n * (↑n : ℝ) = (-1 : ℝ) := by
      have h6 : (↑n : ℝ) ≠ 0 := by
        have h7 : (↑n : ℝ) ≠ (0 : ℝ) := by
          have h8 : (↑n : ℝ) > (0 : ℝ) := by
            have h9 : n > 0 := by
              omega
            have h10 : (↑n : ℝ) = (↑n : ℝ) := rfl
            positivity
          nlinarith
        tauto
      field_simp at *
      <;> ring

    rw [h5] at h4
    linarith

  rw [h2, h3]
  have h4 : (-1 : ℝ) ^ n * ((1991 : ℝ) ^ (-1 : ℝ)) = (-1) ^ n / 1991 := by
    have h6 : ((1991 : ℝ) ^ (-1 : ℝ)) = (1 / 1991 : ℝ) := by
      norm_num
    rw [h6]
    all_goals
      ring

  linarith [h4]