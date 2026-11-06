import Mathlib

/- What is the value of 2−(−2)^(−2)?
(A) −2  (B) 1/16  (C) 7/4 (D) 9/4 (E) 6-/
theorem algebra_96678 : 2 - (-2 : ℝ) ^ (-2 : ℝ) = 7 / 4 := by ring
--it is a simple algebraic calculation with integers