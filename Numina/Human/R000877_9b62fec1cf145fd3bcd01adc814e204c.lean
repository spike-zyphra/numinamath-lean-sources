import Mathlib

/- Mike paid $\$1.25$ for a stamp three years ago. He was just offered double that amount for the stamp. Assuming the stamp's offer price doubles every three years, how many dollars will he be offered in 12 more years? -/
theorem algebra_18781 {x : ℝ} (hx : x = 1.25) : (2 ^ (1 + 12 / 3)) * x = 40 := by
  rw [hx]
  norm_num
