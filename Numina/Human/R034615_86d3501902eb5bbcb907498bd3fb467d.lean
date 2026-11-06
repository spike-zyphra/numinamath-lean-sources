import Mathlib

/- Betty used a calculator to find the product 0.075×2.56. 
She forgot to enter the decimal points.  The calculator showed 19200.  
If Betty had entered the decimal points correctly, the answer would have been
(A) .0192(B) .192(C) 1.92(D) 19.2(E) 192 -/

theorem algebra_96973 : (75:ℚ) / (1000:ℚ) * (256:ℚ) / (100:ℚ) = (19200:ℚ) / (100000:ℚ) := by
--The key here is to cast the numbers above correctly. Then it becomes mere computation
  ring