import Mathlib
set_option exponentiation.threshold 2100

/-2000(2000 ^ 2000 ) = ? 
(A) 2000 ^ 2001 (B) 4000 ^ 2000 (C) 2000 ^ 4000 (D) 4,000,000 ^ 2000 (E) 2000 ^ 4,000,000
-/
theorem algebra_1113 : 2000 * (2000 ^ (2000)) = 2000 ^ 2001 := by
  calc 2000 * (2000 ^ 2000) = 2000 ^ (2000 + 1)
    := by ring -- here we expand using the rules of exponents
  _ = 2000 ^ 2001
    := by ring -- this becomes simple addition of the exponents which gives the solution
/- The solution is (A)
-/