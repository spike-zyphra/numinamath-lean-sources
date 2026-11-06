import Mathlib

theorem algebra_114835 (x y : ℤ) :
    x^2 - x * y + y^2 = x + y ↔
    (x = 1 ∧ y = 2) ∨
    (x = 2 ∧ y = 2) ∨
    (x = 0 ∧ y = 0) ∨
    (x = 1 ∧ y = 0) ∨
    (x = 0 ∧ y = 1) ∨
    (x = 2 ∧ y = 1) := by
  constructor
  · -- Forward direction: if the equation holds, then one of the solutions must hold
    intro h_eq
    have h1 : x ≤ 4 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y)]
    have h2 : x ≥ -3 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y)]
    have h3 : y ≤ 4 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y)]
    have h4 : y ≥ -3 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y)]
    interval_cases x <;> interval_cases y <;> omega
  · -- Backward direction: each given solution satisfies the equation
    rintro (h | h | h | h | h | h)
    all_goals
      rw [h.1, h.2]
      all_goals norm_num