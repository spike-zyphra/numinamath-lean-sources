import Mathlib

/--
What is the value of `2^(1+2+3) - (2^1 + 2^2 + 2^3)`?

(A) 0  
(B) 50  
(C) 52  
(D) 54  
(E) 57
-/
theorem algebra_93992 :
    2 ^ (1 + 2 + 3) - (2 ^ 1 + 2 ^ 2 + 2 ^ 3) = 50 := by
    -- The `norm_num` automatically expands `2^(1+2+3)` into `2^6` and sums/subtracts accordingly.
  norm_num