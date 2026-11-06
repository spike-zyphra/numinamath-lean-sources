import Mathlib

theorem inequalities_297917 (x y z : ℝ) (h : x + y + z = 1) :
    x^2 + y^2 + z^2 ≥ 1 / 3 := by
  have h1 : z = 1 - x - y := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - (1 / 3)), sq_nonneg (y - (1 / 3)), sq_nonneg ((1 - x - y) - (1 / 3)), 
          sq_nonneg (x + y - (2 / 3)), sq_nonneg (x + y - (1 - x - y)), sq_nonneg (x - y),
          sq_nonneg (x - (y)), sq_nonneg (x - (1 - x - y) ), sq_nonneg (y - (1 - x - y) ) ]