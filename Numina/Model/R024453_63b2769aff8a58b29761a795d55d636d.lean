import Mathlib

theorem algebra_161308 (x : ℝ) (hx : x = (26 - 15 * Real.sqrt 3) ^ ((1 : ℝ) / 3)) :
    (7 - 4 * Real.sqrt 3) / x = 2 - Real.sqrt 3 := by

  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith)
  have h2 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [h1]
      _ = 9 := by norm_num

  have h3 : (26 - 15 * Real.sqrt 3 : ℝ) > 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), h1, Real.sqrt_nonneg 3]

  have h4 : (26 - 15 * Real.sqrt 3 : ℝ) = (2 - Real.sqrt 3) ^ 3 := by
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), h1, Real.sqrt_nonneg 3, h3]

  have h5 : x = (2 - Real.sqrt 3) := by
    rw [hx]
    have h6 : (26 - 15 * Real.sqrt 3 : ℝ) = (2 - Real.sqrt 3) ^ 3 := h4
    rw [h6]
    have h7 : (( (2 - Real.sqrt 3) ^ 3 ) : ℝ) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 3) := by
      have h3_pos : (2 - Real.sqrt 3 : ℝ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 3, h1, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
      rw [show (( (2 - Real.sqrt 3) ^ 3 ) : ℝ) = ( (2 - Real.sqrt 3) ) ^ 3 by ring]
      have h4_pos : ( (2 - Real.sqrt 3) : ℝ) ≥ 0 := h3_pos
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    linarith

  have h6 : (2 - Real.sqrt 3 : ℝ) ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, h1]

  rw [h5]
  have eq1 : (7 - 4 * Real.sqrt 3) / (2 - Real.sqrt 3 : ℝ) = 2 - Real.sqrt 3 := by
    have h7 : (2 - Real.sqrt 3 : ℝ) ≠ 0 := h6
    field_simp [(show (2 - Real.sqrt 3 : ℝ) ≠ 0 by exact h7), h1]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), h1, sq_nonneg (2 - Real.sqrt 3), sq_nonneg (2 + Real.sqrt 3)]
  linarith [eq1]