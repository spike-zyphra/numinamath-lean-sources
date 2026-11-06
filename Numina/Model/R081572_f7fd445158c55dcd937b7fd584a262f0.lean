import Mathlib

theorem number_theory_321901 (x y : ℤ) :
    x > 0 ∧ y > 0 ∧ x^2 + 3 * y^2 = 2007 ↔ (x = 42 ∧ y = 9) := by
  constructor
  · -- Assume x and y are positive integers such that x^2 + 3 * y^2 = 2007, prove x = 42 and y = 9.
    rintro ⟨hx, hy, heq⟩
    have h1 : x ≤ 44 := by nlinarith
    have h2 : y ≤ 25 := by nlinarith
    interval_cases x <;> interval_cases y
    <;> omega
  · -- Assume x = 42 and y = 9, prove x and y are positive integers such that x^2 + 3 * y^2 = 2007.
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num