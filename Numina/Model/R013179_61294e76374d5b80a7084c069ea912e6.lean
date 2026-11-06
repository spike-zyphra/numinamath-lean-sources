import Mathlib

theorem algebra_2494 : (54 : ℝ) ^ ((1 : ℝ) / 3) - (250 ^ ((1 : ℝ) / 3)) + (16 ^ ((1 : ℝ) / 3)) = 0 := by
  have h1 : (54 : ℝ) ^ ((1 : ℝ) / 3) = 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h6 : (54 : ℝ) ^ ((1 : ℝ) / 3) = (3 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) := by
      rw [show (54 : ℝ) = (3 ^ 3 * (2 : ℝ) ) by norm_num]
    rw [h6]
    have h541 : (3 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) = (3 : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 3) ) := by
      have h542 : (3 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) = ((3 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
        have h543 : (3 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) = ((3 : ℝ) ^ (3 : ℕ) ) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
          rw [← Real.mul_rpow]
          all_goals positivity
        norm_cast at h543 ⊢
      have h544 : ((3 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (3 : ℝ) := by
        have h545 : ((3 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (3 : ℝ) ^ (3 * (1 / 3 : ℝ) ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          all_goals linarith
        rw [h545]
        norm_num at *
      rw [h544] at h542
      linarith [h542]
    linarith [h541]
  have h2 : (250 : ℝ) ^ ((1 : ℝ) / 3) = 5 * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h6 : (250 : ℝ) ^ ((1 : ℝ) / 3) = (5 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) := by
      rw [show (250 : ℝ) = (5 ^ 3 * (2 : ℝ) ) by norm_num]
    rw [h6]
    have h541 : (5 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) = (5 : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 3) ) := by
      have h542 : (5 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) = ((5 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
        have h543 : (5 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) = ((5 : ℝ) ^ (3 : ℕ) ) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
          rw [← Real.mul_rpow]
          all_goals positivity
        norm_cast at h543 ⊢
      have h544 : ((5 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (5 : ℝ) := by
        have h545 : ((5 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (5 : ℝ) ^ (3 * (1 / 3 : ℝ) ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          all_goals linarith
        rw [h545]
        norm_num at *
      rw [h544] at h542
      linarith [h542]
    linarith [h541]
  have h3 : (16 : ℝ) ^ ((1 : ℝ) / 3) = 2 * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    have h6 : (16 : ℝ) ^ ((1 : ℝ) / 3) = (2 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) := by
      rw [show (16 : ℝ) = (2 ^ 3 * (2 : ℝ) ) by norm_num]
    rw [h6]
    have h541 : (2 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) = (2 : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 3) ) := by
      have h542 : (2 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
        have h543 : (2 ^ 3 * (2 : ℝ) ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ (3 : ℕ) ) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
          rw [← Real.mul_rpow]
          all_goals positivity
        norm_cast at h543 ⊢
      have h544 : ((2 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
        have h545 : ((2 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ (3 * (1 / 3 : ℝ) ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          all_goals linarith
        rw [h545]
        norm_num at *
      rw [h544] at h542
      linarith [h542]
    linarith [h541]
  rw [h1, h2, h3]
  ring