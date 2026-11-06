import Mathlib
open Real

/- What is the value in simplest form of the following expression?
√(1)+√(1+3)+√(1+3+5)+√(1+3+5+7)
(A) 5 (B) 4+√7+√10 (C) 10 (D) 15 (E) 4+3√3+2√5+√7 -/
theorem algebra_93706 : Real.sqrt 1 + Real.sqrt (1 + 3) + Real.sqrt (1 + 3 + 5) + Real.sqrt (1 + 3 + 5 + 7) = 10 := by 
  -- solve by calculating each sum in the square root and then we can discover those sums are all squares of integers. We rewrite the formula into the explicit form showing the squares then we can simplify the formula, getting rid of those square roots, thus getting the result.
  norm_num
  have h:1 + √(2*2) + √(3*3) + √(4*4) = 10 := by simp;norm_num
  convert h;repeat norm_num