import Mathlib

/- A train car held $6000$ pounds of mud which was $88$ percent water. Then the train car sat in the sun, and some of the water evaporated so that now the mud is only $82$ percent water. How many pounds does the mud weigh now? -/
theorem algebra_57209 {x : ℝ} (hx : x ≠ 0) (h : (1 - 88 / 100) * 6000 = (1 - 82 / 100) * x) :
    x = 4000 := by 
  field_simp at h
  linarith