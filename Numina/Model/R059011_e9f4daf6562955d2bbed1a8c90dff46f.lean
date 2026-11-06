import Mathlib

theorem algebra_35790 (r b y : ℕ) (h₀ : r + b + y = 15) :
    r * 1 + b * (2 * r) + y * (3 * b) ≤ 168 := by 
  have h1 : y = 15 - r - b := by
    omega
  rw [h1]
  have h2 : r ≤ 15 := by
    omega
  have h3 : b ≤ 15 := by
    omega
  interval_cases r <;> interval_cases b <;> omega