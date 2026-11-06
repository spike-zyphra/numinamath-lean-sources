import Mathlib

/-
The least common multiple (LCM) of the integers $ a_{1}, a_{2}, \ldots, a_{n} $, which are not all zero, is defined as the smallest positive integer that is divisible by all the integers $ a_{1}, a_{2}, \ldots, a_{n} $. It is denoted by $ [a_{1}, a_{2}, \ldots, a_{n}] $.
a) Calculate $ [6,10,15] $ and $ [7,11,13] $.
-/
theorem number_theory_4589_1 :
  lcm 6 (lcm 10 15) = 30 ∧ lcm 7 (lcm 11 13) = 1001 := by native_decide

/-
The least common multiple (LCM) of the integers $ a_{1}, a_{2}, \ldots, a_{n} $, which are not all zero, is defined as the smallest positive integer that is divisible by all the integers $ a_{1}, a_{2}, \ldots, a_{n} $. It is denoted by $ [a_{1}, a_{2}, \ldots, a_{n}] $.
b) Prove that $ [a_{1}, a_{2}, \ldots, a_{n-1}, a_{n}] = [[a_{1}, a_{2}, \ldots, a_{n-1}], a_{n}] $.
-/
-- There is no definition of lcm for sets in Lean.
