import Mathlib

theorem algebra_297934 {a : ℝ} (ha : a = (Real.sqrt 5 - 1) / 2) :
    ((a^5 + a^4 - 2 * a^3 - a^2 - a + 2) / (a^3 - a)) = -2 := by

  have ha2 : a^2 = 1 - a := by
    rw [ha]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have ha3 : a^3 = 2 * a - 1 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (1 - a) := by rw [ha2]
      _ = a - a^2 := by ring
      _ = a - (1 - a) := by rw [ha2]
      _ = 2 * a - 1 := by ring
  have ha4 : a^4 = 2 - 3 * a := by
    calc
      a^4 = (a^2) ^ 2 := by ring
      _ = (1 - a) ^ 2 := by rw [ha2]
      _ = 1 - 2 * a + a^2 := by ring
      _ = 1 - 2 * a + (1 - a) := by rw [ha2]
      _ = 2 - 3 * a := by ring
  have ha5 : a^5 = 5 * a - 3 := by
    calc
      a^5 = a * a^4 := by ring
      _ = a * (2 - 3 * a) := by rw [ha4]
      _ = 2 * a - 3 * a^2 := by ring
      _ = 2 * a - 3 * (1 - a) := by rw [ha2]
      _ = 5 * a - 3 := by ring
  have h1 : a^3 - a = a - 1 := by
    nlinarith [ha2, ha3]
  have h2 : a^5 + a^4 - 2 * a^3 - a^2 - a + 2 = -2 * a + 2 := by
    nlinarith [ha2, ha3, ha4, ha5]
  have h3 : a - 1 ≠ 0 := by
    by_contra h
    have ha1 : a = 1 := by linarith
    rw [ha] at ha1
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h4 : (a^5 + a^4 - 2 * a^3 - a^2 - a + 2) / (a^3 - a) = -2 := by
    have h5 : a^3 - a = a - 1 := h1
    rw [h5]
    have h5' : a - 1 ≠ 0 := h3
    field_simp [h5']
    <;> nlinarith [h2]
  exact h4