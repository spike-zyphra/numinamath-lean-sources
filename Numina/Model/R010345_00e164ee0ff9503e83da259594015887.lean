import Mathlib

theorem algebra_17177 (x y : ℝ) (h1 : y = -4 * x) (h2 : y - 2 = 12 * x) :
    (x, y) = (-1 / 8, 1 / 2) := by 
  have hx : x = -1 / 8 := by
    linarith [h1, h2]
  
  have hy : y = 1 / 2 := by
    rw [hx] at h1 -- substitute x = -1/8 into y = -4 * x
    linarith
  
  simp [Prod.ext_iff, hx, hy]
  <;> linarith
  all_goals tauto