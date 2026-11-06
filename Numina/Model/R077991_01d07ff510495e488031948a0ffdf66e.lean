import Mathlib

theorem algebra_8029 {a : ℝ} (ha : a ^ 2 - a - 1 = 0) : a ^ 3 - 2011 * a ^ 2 + 2009 * a - 2010 = -4020 := by 
  have h1 : a ^ 2 = a + 1 := by linarith
  have h2 : a ^ 3 = 2 * a + 1 := by
    calc
      a ^ 3 = a * a ^ 2 := by ring
      _ = a * (a + 1) := by rw [h1]
      _ = a ^ 2 + a := by ring
      _ = (a + 1) + a := by rw [h1]
      _ = 2 * a + 1 := by ring
  rw [h2, h1]
  linarith