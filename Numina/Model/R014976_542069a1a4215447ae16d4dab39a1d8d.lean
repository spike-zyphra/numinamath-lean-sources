import Mathlib

open Real

theorem inequalities_159439 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) / 2 ≥ sqrt (x * y) := by
  have h1 : ( (x + y) / 2 ) ^ 2 ≥ x * y := by
    nlinarith [sq_nonneg (x - y)]
  
  have h2 : (x * y) ≥ 0 := mul_nonneg hx hy
  
  have h3 : ( (x + y) / 2 ) ≥ 0 := by
    linarith [hx, hy]

  have h4 : sqrt (( (x + y) / 2 ) ^ 2) = (x + y) / 2 := by
    rw [Real.sqrt_sq]
    linarith [h3]

  have h5 : sqrt (x * y) ≤ (x + y) / 2 := by
    have h6 : sqrt (x * y) ≤ sqrt (( (x + y) / 2 ) ^ 2) := Real.sqrt_le_sqrt (by linarith [h1, h2])
    rw [h4] at h6
    linarith [h6]

  linarith [h5]