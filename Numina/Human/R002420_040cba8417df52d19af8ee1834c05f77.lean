import Mathlib

/- What is
2+4+61+3+5−1+3+52+4+6 ?
(A) −1 (B) 5/36 (C) 7/12 (D) 147/60 (E) 43/3-/
theorem algebra_93126 : (2 + 4 + 6 : ℚ) / (1 + 3 + 5) - (1 + 3 + 5) / (2 + 4 + 6) = 7 / 12 := by 
  -- There is not much to do here, just to evaluate the fraction using the usual rules for adding fractions.
  norm_num