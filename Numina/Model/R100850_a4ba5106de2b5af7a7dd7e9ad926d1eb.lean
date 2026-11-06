import Mathlib

theorem algebra_160847 (x y : ℤ) : x^2 + y^2 = x + y + 2 ↔
    (x = -1 ∧ y = 1) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = -1) ∨
    (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = -1) ∨ (x = 1 ∧ y = 2) ∨
    (x = 2 ∧ y = 1) ∨ (x = 2 ∧ y = 0) := by

  constructor
  · -- Assume the equation holds; deduce the possible values for x and y
    intro h
    have h1 : x ≤ 2 := by 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x + 1), sq_nonneg (y + 1)]
    have h2 : y ≤ 2 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x + 1), sq_nonneg (y + 1)]
    have h3 : x ≥ -1 := by 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x + 1), sq_nonneg (y + 1)]
    have h4 : y ≥ -1 := by 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x + 1), sq_nonneg (y + 1)]
    
    interval_cases x <;> interval_cases y
      <;> omega

  · -- Show that each of the listed solutions satisfies the equation
    rintro (h | h | h | h | h | h | h | h)
    · -- Case (-1, 1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (-1, 0)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (0, -1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (0, 2)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (1, -1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (1, 2)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (2, 1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (2, 0)
      rcases h with ⟨rfl, rfl⟩
      norm_num