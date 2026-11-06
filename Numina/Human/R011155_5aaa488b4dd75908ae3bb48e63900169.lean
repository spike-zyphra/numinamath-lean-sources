import Mathlib
open Real

/- In our number system the base is ten. If the base were changed to four you would
count as follows: 1, 2, 3, 10, 11, 12, 13, 20, 21, 22, 23, 30, ... The twentieth number would be:
(A) 20  (B) 38  (C) 44 (D) 104 (E) 110 -/
theorem number_theory_96442 : Nat.digits 4 20 = [0, 1, 1] :=by
  -- solve by expanding 20(base 10) into base 4
  -- since we have 20(10)=1*4^2+1*4^1+0*4^0, we can see 20(10)=110(4)
  simp