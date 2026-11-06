import Mathlib

theorem algebra_190194 (x y : ℤ) :
    3 * x ^ 2 + 3 * y ^ 2 - 18 * x + 12 * y + 27 = 0 ↔
    (x = 3 ∧ y = 0) ∨ (x = 3 ∧ y = -4) ∨ (x = 1 ∧ y = -2) ∨ (x = 5 ∧ y = -2) := by 
  constructor
  · -- Assume 3x^2 + 3y^2 - 18x + 12y + 27 = 0
    rintro h
    have h1 : (x - 3) ^ 2 + (y + 2) ^ 2 = 4 := by
      nlinarith
    have h2 : x - 3 ≤ 2 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (y + 2)]
    have h3 : x - 3 ≥ -2 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (y + 2)]
    have h4 : y + 2 ≤ 2 := by nlinarith [sq_nonneg (y + 2), sq_nonneg (x - 3)]
    have h5 : y + 2 ≥ -2 := by nlinarith [sq_nonneg (y + 2), sq_nonneg (x - 3)]
    interval_cases h6 : x - 3 <;> interval_cases h7 : y + 2 <;> omega
  · -- Show that the given points satisfy the equation
    rintro (h | h | h | h)
    · -- First point (3, 0)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Second point (3, -4)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Third point (1, -2)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Fourth point (5, -2)
      rcases h with ⟨rfl, rfl⟩
      norm_num