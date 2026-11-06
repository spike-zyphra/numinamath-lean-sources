import Mathlib

theorem algebra_299815 (x y : ℤ) :
    2 * x ^ 2 + x * y + y ^ 2 - x + 2 * y + 1 = 0 ↔
    (x = 0 ∧ y = -1) ∨ (x = 1 ∧ y = -1) ∨ (x = 1 ∧ y = -2) := by 
  constructor
  · -- Forward implication: equation implies solutions 
    intro h
    have h1 : x ≤ 2 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - y), sq_nonneg (x + 2), sq_nonneg (y + 2)]
    have h2 : x ≥ -2 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - y), sq_nonneg (x + 2), sq_nonneg (y + 2)]
    have h3 : y ≤ 1 := by 
      nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - y), sq_nonneg (x + 2), sq_nonneg (y + 2)]
    have h4 : y ≥ -5 := by 
      nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - y), sq_nonneg (x + 2), sq_nonneg (y + 2)]
    interval_cases x <;> interval_cases y <;> omega
  · -- Reverse implication: solutions satisfy the equation
    rintro (h | h | h)
    · -- First solution (0, -1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Second solution (1, -1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Third solution (1, -2)
      rcases h with ⟨rfl, rfl⟩
      norm_num