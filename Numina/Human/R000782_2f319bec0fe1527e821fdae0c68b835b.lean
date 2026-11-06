import Mathlib

/- The product of two positive integers plus their sum is 95. The integers are relatively prime, and each is less than 20. What is the sum of the two integers? -/
theorem algebra_15249 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hxy : x * y + x + y = 95) (hrel : Nat.Coprime x y) (h20 : x < 20 ∧ y < 20) :
    x + y = 18 := by
  have h : x * y + x + y = 95 := hxy
  have h : x < 20 := h20.1
  have h : y < 20 := h20.2
  interval_cases x <;> interval_cases y <;> simp_all (config := {decide := true})