import Mathlib

theorem algebra_328145 {x : ℝ} (hx : x = (Real.sqrt 5 - 1) / 2) : x^4 + x^2 + 2 * x - 1 = 3 - Real.sqrt 5 := by
  have h1 : x^2 = -x + 1 := by
    rw [hx]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h2 : x^4 = -3 * x + 2 := by
    calc
      x^4 = (x^2) ^ 2 := by ring
      _ = (-x + 1) ^ 2 := by rw [h1]
      _ = x^2 - 2 * x + 1 := by ring
      _ = (-x + 1) - 2 * x + 1 := by rw [h1]
      _ = -3 * x + 2 := by ring
  have h3 : x^4 + x^2 + 2 * x - 1 = -2 * x + 2 := by
    rw [h2]
    have y : x^2 = -x + 1 := h1
    rw [y]
    ring
  rw [h3, hx]
  ring