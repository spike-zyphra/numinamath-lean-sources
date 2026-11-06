import Mathlib

/- The number 1341 can be written as the sum of three consecutive positive integers. What is the largest of these integers? -/
theorem algebra_21325 (n : ℕ) (h : n > 0) (h' : n + (n + 1) + (n + 2) = 1341) :
    max (max n (n + 1)) (n + 2) = 448 := by
    -- trivial
    omega
