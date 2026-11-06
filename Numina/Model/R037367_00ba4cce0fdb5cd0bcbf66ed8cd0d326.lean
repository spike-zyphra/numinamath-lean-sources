import Mathlib

theorem algebra_257975 : (409 * Real.sqrt 7 + 1082) ^ ((1 : ℝ) / 5) -
    (409 * Real.sqrt 7 - 1082) ^ ((1 : ℝ) / 5) = 4 := by

  have h1 : ((2 + Real.sqrt 7) : ℝ) ^ 5 = (409 * Real.sqrt 7 + 1082 : ℝ) := by
    ring_nf
    have h2 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)
    have h3 : Real.sqrt 7 ^ 3 = 7 * Real.sqrt 7 := by
      calc
        Real.sqrt 7 ^ 3 = Real.sqrt 7 ^ 2 * Real.sqrt 7 := by ring
        _ = 7 * Real.sqrt 7 := by rw [h2]
    have h4 : Real.sqrt 7 ^ 4 = (49 : ℝ) := by
      calc
        Real.sqrt 7 ^ 4 = (Real.sqrt 7 ^ 2) ^ 2 := by ring
        _ = 7 ^ 2 := by rw [h2]
        _ = (49 : ℝ) := by norm_num
    have h5 : Real.sqrt 7 ^ 5 = (49 * Real.sqrt 7 : ℝ) := by
      calc
        Real.sqrt 7 ^ 5 = Real.sqrt 7 ^ 4 * Real.sqrt 7 := by ring
        _ = 49 * Real.sqrt 7 := by rw [h4]
    simp [h2, h3, h4, h5]
    <;> nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), h2]

  have h6 : ((2 - Real.sqrt 7) : ℝ) ^ 5 = (1082 - 409 * Real.sqrt 7 : ℝ) := by
    ring_nf
    have h2 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)
    have h3 : Real.sqrt 7 ^ 3 = 7 * Real.sqrt 7 := by
      calc
        Real.sqrt 7 ^ 3 = Real.sqrt 7 ^ 2 * Real.sqrt 7 := by ring
        _ = 7 * Real.sqrt 7 := by rw [h2]
    have h4 : Real.sqrt 7 ^ 4 = (49 : ℝ) := by
      calc
        Real.sqrt 7 ^ 4 = (Real.sqrt 7 ^ 2) ^ 2 := by ring
        _ = 7 ^ 2 := by rw [h2]
        _ = (49 : ℝ) := by norm_num
    have h5 : Real.sqrt 7 ^ 5 = (49 * Real.sqrt 7 : ℝ) := by
      calc
        Real.sqrt 7 ^ 5 = Real.sqrt 7 ^ 4 * Real.sqrt 7 := by ring
        _ = 49 * Real.sqrt 7 := by rw [h4]
    simp [h2, h3, h4, h5]
    <;> nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), h2]

  have h7 : ((409 * Real.sqrt 7 + 1082 : ℝ) : ℝ) ^ ((1 : ℝ) / 5) = (2 + Real.sqrt 7 : ℝ) := by
    have h8 : ((2 + Real.sqrt 7) : ℝ) ^ 5 = (409 * Real.sqrt 7 + 1082 : ℝ) := h1
    have h9 : ((409 * Real.sqrt 7 + 1082 : ℝ) : ℝ) = ((2 + Real.sqrt 7 : ℝ) ) ^ 5 := by linarith
    rw [h9]
    have h10 : (((2 + Real.sqrt 7 : ℝ) ) ^ 5 : ℝ) ^ ((1 : ℝ) / 5) = (2 + Real.sqrt 7 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        positivity
    linarith

  have h10 : ((409 * Real.sqrt 7 - 1082 : ℝ) ) ^ ((1 : ℝ) / 5) = - (2 - Real.sqrt 7 : ℝ) := by
    have h11 : (409 * Real.sqrt 7 - 1082 : ℝ) = - ((2 - Real.sqrt 7 : ℝ) ^ 5) := by
      linarith [h6]
    rw [h11]
    have h14 : (- ((2 - Real.sqrt 7 : ℝ) ^ 5) : ℝ) ^ ((1 : ℝ) / 5) = - (2 - Real.sqrt 7 : ℝ) := by
      have h15 : (- ((2 - Real.sqrt 7 : ℝ) ^ 5) : ℝ) = ((- (2 - Real.sqrt 7 : ℝ) ) ^ 5 : ℝ) := by
        ring_nf
      rw [h15]
      have h16 : ((- (2 - Real.sqrt 7 : ℝ) ) ^ 5 : ℝ) ^ ((1 : ℝ) / 5) = - (2 - Real.sqrt 7 : ℝ) := by
        have h17 : ((- (2 - Real.sqrt 7 : ℝ) ) ^ 5 : ℝ) ^ ((1 : ℝ) / 5) = (- (2 - Real.sqrt 7 : ℝ) ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals
            nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num) ]
        linarith
      linarith
    linarith

  rw [h7, h10]
  nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num) ]