import Mathlib

/- What is the value of (11!−10!)/9!?
(A) 99(B) 100(C) 110(D) 121(E) 132 -/
theorem algebra_95580 : (Nat.factorial 11 - Nat.factorial 10) / Nat.factorial 9 = 100 := by
--it is an arithmetic calculation with positive integers
rfl