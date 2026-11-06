import Mathlib

theorem algebra_323967 {a : ℝ} (ha : a = √7 - 1) : 3 * a^3 + 12 * a^2 - 6 * a - 12 = 24 := by
  have ha1 : a + 1 = Real.sqrt 7 := by
    rw [ha]
    ring
  have ha2 : (a + 1)^2 = 7 := by 
    rw [ha1]
    have h : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)
    linarith
  have h1 : a^2 + 2 * a - 6 = 0 := by
    nlinarith [ha2]
  have ha3 : a^3 = 10 * a - 12 := by
    have h2 : a^2 = -2 * a + 6 := by
      linarith [h1]
    calc
      a^3 = a * a^2 := by ring
      _ = a * (-2 * a + 6) := by rw [h2]
      _ = -2 * a^2 + 6 * a := by ring
      _ = -2 * (-2 * a + 6) + 6 * a := by rw [h2]
      _ = 10 * a - 12 := by ring
  have h2 : a^2 = -2 * a + 6 := by 
    linarith [h1]
  rw [ha3]
  rw [show a^2 = -2 * a + 6 by linarith [h2]]
  nlinarith [Real.sqrt_nonneg 7]