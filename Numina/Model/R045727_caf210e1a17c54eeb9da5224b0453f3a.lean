import Mathlib
open Real

theorem algebra_94246 {x y : ℝ} (hy : y ≠ 0) (h : x / y = 3 / 4) :
(x - y) / y ≠ 1 / 4 := by 
  by_contra h1
  have h2 : x / y - 1 = -1 / 4 := by
    have h3 : x / y = 3 / 4 := h
    linarith 
  have h3 : (x - y) / y = x / y - 1 := by
    field_simp [hy]
    <;> linarith 
  have h4 : x / y - 1 = 1 / 4 := by
    have eq1 : (x - y) / y = x / y - 1 := h3
    linarith [h1, eq1] 
  linarith [h2, h4]