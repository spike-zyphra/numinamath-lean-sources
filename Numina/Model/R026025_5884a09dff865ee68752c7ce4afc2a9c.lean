import Mathlib

theorem number_theory_129770 (x y : ℤ) : x^2 + x * y + y^2 = 1 ↔
    (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 1 ∧ y = -1) ∨
    (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨ (x = -1 ∧ y = 1) := by
  constructor
  · -- Assume x^2 + x * y + y^2 = 1, prove the disjunction of the 6 pairs
    rintro h
    have h1 : x ≤ 2 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
    have h2 : x ≥ -2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y), sq_nonneg (x + 1), sq_nonneg (y + 1)]
    have h3 : y ≤ 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (y - 1), sq_nonneg (x - 1)]
    have h4 : y ≥ -2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (y + 1), sq_nonneg (x + 1)]
    interval_cases x <;> interval_cases y <;> omega
  · -- Assume the disjunction, prove x^2 + x * y + y^2 = 1
    rintro (h | h | h | h | h | h)
    · -- Case (1, 0)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (-1, 0)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (1, -1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (0, 1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (0, -1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (-1, 1)
      rcases h with ⟨rfl, rfl⟩
      norm_num