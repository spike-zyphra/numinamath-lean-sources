import Mathlib

theorem algebra_313880 {a : ℝ} (ha : a = (Real.sqrt 5 - 1) / 2) :
    ((a^5 + a^4 - 2 * a^3 - a^2 - a + 2) / (a^3 - a)) = -2 := by
  have h1 : a^2 = 1 - a := by
    rw [ha]
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h2 : a^3 = 2 * a - 1 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (1 - a) := by rw [h1]
      _ = a - a^2 := by ring
      _ = a - (1 - a) := by rw [h1]
      _ = 2 * a - 1 := by ring
  have h3 : a^4 = 2 - 3 * a := by
    calc
      a^4 = a * a^3 := by ring
      _ = a * (2 * a - 1) := by rw [h2]
      _ = 2 * a^2 - a := by ring
      _ = 2 * (1 - a) - a := by rw [h1]
      _ = 2 - 3 * a := by ring
  have h4 : a^5 = 5 * a - 3 := by
    calc
      a^5 = a * a^4 := by ring
      _ = a * (2 - 3 * a) := by rw [h3]
      _ = 2 * a - 3 * a^2 := by ring
      _ = 2 * a - 3 * (1 - a) := by rw [h1]
      _ = 5 * a - 3 := by ring
  have hn : a^5 + a^4 - 2 * a^3 - a^2 - a + 2 = -2 * a + 2 := by
    rw [h4, h3, h2, h1]
    nlinarith
  have hd : a^3 - a = a - 1 := by
    rw [h2]
    ring
  have ha_ne_1 : a - 1 ≠ 0 := by
    intro h
    have ha1 : a = 1 := by linarith
    rw [ha] at ha1
    have h2 : Real.sqrt 5 = 3 := by
      nlinarith
    have h3 : Real.sqrt 5 < 3 := by
      rw [Real.sqrt_lt] <;> norm_num
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (5 : ℝ) > (0 : ℝ) by norm_num)]
  rw [hn, hd]
  field_simp [ha_ne_1]
  <;> nlinarith