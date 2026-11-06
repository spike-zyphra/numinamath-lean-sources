import Mathlib

theorem algebra_3901 (x y : ℤ) (hx : 10 ≤ x ∧ x < 100) (hy : 10 ≤ y ∧ y < 100)
(h : 3 * x ^ 2 - 5 * x * y + 2 * y ^ 2 = 2023) : x = 85 := by
  have h1 : 10 ≤ x := hx.left
  have h2 : x < 100 := hx.right
  have h3 : 10 ≤ y := hy.left
  have h4 : y < 100 := hy.right
  interval_cases x <;> interval_cases y <;> omega