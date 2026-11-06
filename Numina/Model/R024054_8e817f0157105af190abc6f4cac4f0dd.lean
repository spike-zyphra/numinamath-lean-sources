import Mathlib

open Real

theorem inequalities_84288 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : sqrt x - sqrt y = 10) :
    x - 2 * y ≤ 200 := by
  have h1 : sqrt x = sqrt y + 10 := by linarith
  have h2 : x = (sqrt y + 10) ^ 2 := by
    calc
      x = (sqrt x) ^ 2 := by rw [Real.sq_sqrt]; linarith
      _ = (sqrt y + 10) ^ 2 := by rw [h1]
  have h3 : x = y + 20 * sqrt y + 100 := by
    rw [h2]
    have h4 : (sqrt y + 10) ^ 2 = (sqrt y) ^ 2 + 20 * sqrt y + 100 := by
      ring
    rw [h4]
    have h5 : (sqrt y) ^ 2 = y := by 
      rw [Real.sq_sqrt] 
      linarith
    rw [h5]
  have h4 : x - 2 * y = 100 + 20 * sqrt y - y := by
    nlinarith [h3]
  have h5 : 20 * sqrt y - y ≤ 100 := by
    nlinarith [sq_nonneg (sqrt y - 10), Real.sqrt_nonneg y, sq_nonneg (y - 100)]
  nlinarith [h4, h5]