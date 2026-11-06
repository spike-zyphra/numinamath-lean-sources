import Mathlib
open Real

/- Six rectangles each with a common base width of 2 have lengths of 1, 4, 9, 16, 25
and 36. What is the sum of the areas of the six rectangles?
(A) 91 (B) 93 (C) 162  (D) 182 (E) 202 -/
theorem algebra_98159 : 2*1+2*4+2*9+2*16+2*25+2*36 = 182 := by
  -- solve by calculation
  norm_num