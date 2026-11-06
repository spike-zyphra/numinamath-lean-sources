import Mathlib

/- Big Al, the ape, ate 100 bananas from May 1 through May 5. Each day he ate six more bananas than
on the previous day. How many bananas did Big Al eat on May 5?
(A) 20(B) 22(C) 30(D) 32(E) 34 -/

theorem algebra_95712 (a : ℕ) (h : a + (a + 6) + (a + 12) + (a + 18) + (a + 24) = 100) :
a + 24 = 32 := by 
--simplifying algebraically h yields the claim
  omega