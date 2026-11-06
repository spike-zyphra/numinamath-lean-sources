import Mathlib
import Mathlib.Tactic.NormNum

/--
What is the value of \(\frac{(2112 - 2021)^2}{169}\)?

(A) 7  
(B) 21  
(C) 49  
(D) 64  
(E) 91  
-/
theorem algebra_92934 :
    ((2112 - 2021) ^ 2) / 169 = 49 := by
    -- The tactic `norm_num` automatically expands (2112 - 2021)^2 and then divides by 169.
  norm_num