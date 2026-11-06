import Mathlib

theorem algebra_265620 (x y : ℤ) : x^2 + y^2 + x + y = 4 ↔ (x = 1 ∧ y = 1) ∨ (x = 1 ∧ y = -2) ∨ (x = -2 ∧ y = 1) ∨ (x = -2 ∧ y = -2) := by
  constructor
  · -- Forward implication: If x^2 + y^2 + x + y = 4, then (x, y) is in the boxed set.
    rintro H
    have h₁ : x ≥ -3 := by
      nlinarith [sq_nonneg (x + 2), sq_nonneg (y + 2)]
    have h₂ : x ≤ 2 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
    have h₃ : y ≥ -3 := by
      nlinarith [sq_nonneg (x + 2), sq_nonneg (y + 2)]
    have h₄ : y ≤ 2 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
    interval_cases x <;> interval_cases y
    <;> omega
  · -- Reverse direction: If (x, y) is in the boxed set, then x^2 + y^2 + x + y = 4.
    rintro (h | h | h | h)
    · -- Case (1,1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (1,-2)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (-2,1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (-2,-2)
      rcases h with ⟨rfl, rfl⟩
      norm_num