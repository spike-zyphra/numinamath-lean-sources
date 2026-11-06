import Mathlib

theorem algebra_65549 (x y z : ℕ) (h : x + y + z = 10) :
    x^2 + 5 * y + z^3 ≥ 37 := by
  have h1 : z ≤ 10 := by
    omega
  have h2 : x ≤ 10 := by
    omega
  have h3 : y ≤ 10 := by
    omega
  interval_cases z <;> interval_cases x <;> omega