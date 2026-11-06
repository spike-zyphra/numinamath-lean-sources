import Mathlib

theorem algebra_254280 {x : ℝ} (hx : x = Real.sqrt 7 + Real.sqrt 6) :
    (x + 1/x) / (x - 1/x) = Real.sqrt 7 / Real.sqrt 6 := by

  have hx1 : x ≠ 0 := by
    rw [hx]
    have h1 : Real.sqrt 7 + Real.sqrt 6 > 0 := by
      have h7 : Real.sqrt 7 > 0 := by positivity
      have h6 : Real.sqrt 6 > 0 := by positivity
      linarith
    linarith

  have h1xp : 1 / x = Real.sqrt 7 - Real.sqrt 6 := by
    rw [hx]
    field_simp [hx1]
    have hdenom : (Real.sqrt 7 + Real.sqrt 6) * (Real.sqrt 7 - Real.sqrt 6) = 1 := by
      calc
        (Real.sqrt 7 + Real.sqrt 6) * (Real.sqrt 7 - Real.sqrt 6)
            = (Real.sqrt 7) ^ 2 - (Real.sqrt 6) ^ 2 := by ring
        _ = 7 - 6 := by simp [Real.sq_sqrt]
        _ = 1 := by norm_num
    nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]

  have h2 : x + 1 / x = 2 * Real.sqrt 7 := by
    rw [h1xp, hx]
    ring

  have h3 : x - 1 / x = 2 * Real.sqrt 6 := by
    rw [h1xp, hx]
    ring

  rw [h2, h3]
  have h4 : Real.sqrt 6 ≠ 0 := by positivity
  field_simp [h4]
  <;> ring_nf <;> simp [Real.sq_sqrt] <;> ring