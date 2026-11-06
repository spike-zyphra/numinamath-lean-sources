import Mathlib

theorem algebra_197922 (x y : ℝ) (h : 2 * x + 5 * y = 3) (c : ℝ)
    (hc : c = Real.sqrt (4 ^ (x + 1 / 2) * 32 ^ y)) : c = 4 := by
  have h1 : c = Real.sqrt (4 ^ (x + 1 / 2) * 32 ^ y) := by
    rw [hc]

  have h2 : (4:ℝ) ^ (x + 1/2) = (2:ℝ) ^ (2 * (x + 1/2)) := by
    rw [show (4:ℝ) = (2:ℝ) ^ (2:ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals nlinarith

  have h3 : (32:ℝ) ^ (y:ℝ) = (2:ℝ) ^ (5 * y:ℝ) := by
    rw [show (32:ℝ) = (2:ℝ) ^ (5:ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals nlinarith

  have h4 : (4:ℝ) ^ (x + 1/2) * (32:ℝ) ^ (y:ℝ) = (16:ℝ) := by
    rw [h2, h3]

    have h5 : 2 * (x + 1/2) + 5 * y = 4 := by
      linarith [h]

    have h6 : (2:ℝ) ^ (2 * (x + 1/2)) * (2:ℝ) ^ (5 * y) = (2:ℝ) ^ (2 * (x + 1/2) + 5 * y) := by
      rw [← Real.rpow_add]
      all_goals linarith

    rw [h6]
    rw [show 2 * (x + 1/2) + 5 * y = (4:ℝ) by linarith [h]]
    norm_num

  have h5 : Real.sqrt (4 ^ (x + 1 / 2) * 32 ^ y) = 4 := by
    rw [show (4:ℝ) ^ (x + 1/2) * (32:ℝ) ^ (y:ℝ) = (16:ℝ) by linarith [h4]]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  rw [h1]
  exact h5