import Mathlib
theorem algebra_611461 : ∏ i ∈ Finset.range 2005, (((i + 2) ^ 2 : ℝ) / ((i + 2) ^ 2 - 1)) = 4012 / 2007:= by
  norm_num
  <;> native_decide