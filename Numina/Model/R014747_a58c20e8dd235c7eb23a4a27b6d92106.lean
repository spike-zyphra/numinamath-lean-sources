import Mathlib

theorem algebra_10076 (x y : ℕ) (h₀ : 5 ∣ x + 2 * y) (h₁ : 3 ∣ x + y)
    (h₂ : 99 ≤ 2 * x + y) :
    7 * x + 5 * y ≥ 366 := by
  by_contra h
  push_neg at h
  have h3 : x ≤ 51 := by
    omega
  have h4 : y ≤ 52 := by
    omega
  interval_cases x <;> omega