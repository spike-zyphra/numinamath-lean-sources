import Mathlib

theorem algebra_321607 {a b : ℝ} (ha : a = 1 / (2 + Real.sqrt 7)) (hb : b = 1 / (2 - Real.sqrt 7)) :
    a^3 - a + b^3 - b = -64 / 27 := by
  have h1 : a + b = -4 / 3 := by
    rw [ha, hb]
    have h2 : (2 + Real.sqrt 7) ≠ 0 := by
      have h3 : Real.sqrt 7 > 0 := Real.sqrt_pos.mpr (show 7 > (0 : ℝ) by norm_num)
      have h4 : (2 + Real.sqrt 7) > 2 := by linarith
      positivity
    have h10 : 2 - Real.sqrt 7 ≠ 0 := by
      have h9 : Real.sqrt 7 > 0 := by positivity
      intro h
      have h7 : Real.sqrt 7 = (2 : ℝ) := by linarith
      have h10 : Real.sqrt 7 ^ 2 = (7 : ℝ) := Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num)
      rw [h7] at h10
      nlinarith [h9, Real.sqrt_nonneg (7 : ℝ)]
    field_simp [(show (2 + Real.sqrt 7) ≠ 0 by exact h2), (show (2 - Real.sqrt 7) ≠ 0 by exact h10)]
    nlinarith [Real.sqrt_nonneg (7 : ℝ), Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num)]
  have h3 : a * b = -1 / 3 := by
    rw [ha, hb]
    have h2 : (2 + Real.sqrt 7) ≠ 0 := by
      have h3 : Real.sqrt 7 > 0 := Real.sqrt_pos.mpr (show 7 > (0 : ℝ) by norm_num)
      have h4 : (2 + Real.sqrt 7) > 2 := by linarith
      positivity
    have h10 : 2 - Real.sqrt 7 ≠ 0 := by
      have h9 : Real.sqrt 7 > 0 := by positivity
      intro h
      have h7 : Real.sqrt 7 = (2 : ℝ) := by linarith
      have h10 : Real.sqrt 7 ^ 2 = (7 : ℝ) := Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num)
      rw [h7] at h10
      nlinarith [h9, Real.sqrt_nonneg (7 : ℝ)]
    field_simp [(show (2 + Real.sqrt 7) ≠ 0 by exact h2), (show (2 - Real.sqrt 7) ≠ 0 by exact h10)]
    nlinarith [Real.sqrt_nonneg (7 : ℝ), Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num)]
  have h4 : a^3 + b^3 = -100 / 27 := by
      have h5 : a^3 + b^3 = (a + b)^3 - 3 * (a * b) * (a + b) := by ring
      rw [h5, h1, h3]
      norm_num
  calc
    a^3 - a + b^3 - b = (a^3 + b^3) - (a + b) := by ring
    _ = (-100 / 27) - (-4 / 3) := by rw [h4, h1]
    _ = -64 / 27 := by norm_num