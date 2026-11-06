import Mathlib

/- The product of two positive integers plus their sum is 103. The integers are relatively prime, and each is less than 20. What is the sum of the two integers? -/
theorem algebra_14546 {x y : ℕ} (hx : x < 20) (hy : y < 20)
    (hxy : Nat.Coprime x y) (hsum : x * y + x + y = 103) :
    x + y = 19 := by
  have hx' : x ≤ 19 := by linarith
  have hy' : y ≤ 19 := by linarith
  interval_cases x <;> interval_cases y <;> omega