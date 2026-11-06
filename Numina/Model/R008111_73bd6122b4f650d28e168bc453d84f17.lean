import Mathlib

/-
Problem

"The sum of $x$ and $5$ is a non-positive number." Express this as an inequality.
-/

theorem algebra_9044 (x : ℝ) (h : x + 5 ≤ 0) : x ≤ -5 := by 
  linarith