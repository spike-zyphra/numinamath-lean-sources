import Mathlib

/- The product of two consecutive page numbers is $18{,}360.$ What is the sum of the two page numbers? -/
theorem algebra_10243 {n : ℕ} (h : n * (n + 1) = 18360) : n + (n + 1) = 271 := by 
  nlinarith