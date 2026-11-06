import Mathlib

open Real

-- The area of a triangle computed as (1/2) * |576/5| equals 288/5
theorem triangle_area_is_288_div_5 :
  (1 / 2 : ℝ) * |576 / 5| = 288 / 5 := by
  -- Apply the definition of absolute value: if the number is nonnegative, |x| = x
  rw [abs_of_nonneg]
  -- Simplify the numerical expression: (1/2) * (576/5) = 288/5
  · norm_num
   -- Justify that 576/5 is nonnegative, so we can remove the absolute value
  · norm_num 
