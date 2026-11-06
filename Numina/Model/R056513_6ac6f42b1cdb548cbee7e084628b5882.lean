import Mathlib

theorem algebra_2291 {a : ℝ} (ha : a = Real.sqrt 5 + 3) :
    2*a^3-11*a^2+2*a+1=-3:= by
  have ha2 : a - 3 = Real.sqrt 5 := by 
    rw [ha]
    ring
  have h1 : (a - 3) ^ 2 = 5 := by
    rw [ha2]
    have hsq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)
    linarith [hsq]
  have h2 : a ^ 2 - 6 * a + 4 = 0 := by 
    nlinarith [h1]
  have h3 : a ^ 2 = 6 * a - 4 := by 
    linarith [h2]
  have h4 : a ^ 3 = 32 * a - 24 := by 
    calc
      a ^ 3 = a * a ^ 2 := by ring
      _ = a * (6 * a - 4) := by rw [h3]
      _ = 6 * a ^ 2 - 4 * a := by ring
      _ = 6 * (6 * a - 4) - 4 * a := by rw [h3]
      _ = 36 * a - 24 - 4 * a := by ring
      _ = 32 * a - 24 := by ring
  rw [h4, h3]
  nlinarith