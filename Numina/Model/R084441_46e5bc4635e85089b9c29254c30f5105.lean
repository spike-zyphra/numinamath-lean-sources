import Mathlib

theorem algebra_296775 {x : ℝ} (hx : x^2 - x - 2 = 0) :
    (x^2 - x + 2 * Real.sqrt 3) / (x^4 - 2 * x^3 + x^2 - 1 + Real.sqrt 3) = 2 * Real.sqrt 3 / 3 := by

  have h1 : x^2 = x + 2 := by linarith

  have h2 : x^3 = 3 * x + 2 := by
    calc
      x^3 = x * x^2 := by ring
      _ = x * (x + 2) := by rw [h1]
      _ = x^2 + 2 * x := by ring
      _ = (x + 2) + 2 * x := by rw [h1]
      _ = 3 * x + 2 := by ring

  have h3 : x^4 = 5 * x + 6 := by
    calc
      x^4 = x * x^3 := by ring
      _ = x * (3 * x + 2) := by rw [h2]
      _ = 3 * x^2 + 2 * x := by ring
      _ = 3 * (x + 2) + 2 * x := by rw [h1]
      _ = 5 * x + 6 := by ring
  have h4 : x^4 - 2 * x^3 + x^2 - 1 + Real.sqrt 3 = 3 + Real.sqrt 3 := by
    rw [h3, h2, h1]
    nlinarith [h1]
  have h5 : x^2 - x + 2 * Real.sqrt 3 = 2 + 2 * Real.sqrt 3 := by
    have h6 : x^2 - x = 2 := by
      nlinarith [hx]
    linarith [h6]
  rw [h4, h5]
  field_simp [(show 3 + Real.sqrt 3 ≠ 0 by positivity)]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]