import Mathlib

theorem algebra_161347 (x y : ℤ) :
    x^2 + x * y + y^2 = x + 20 ↔
    (x = 1 ∧ y = -5) ∨ (x = 5 ∧ y = -5) ∨ (x = -4 ∧ y = 0) ∨
    (x = 5 ∧ y = 0) ∨ (x = -4 ∧ y = 4) ∨ (x = 1 ∧ y = 4) := by 
  constructor
  · -- Assume the equation holds, prove the set of solutions
    intro h
    have h1 : x ≥ -5 := by 
      nlinarith [sq_nonneg (x + 4), sq_nonneg (y - 4), sq_nonneg (x - 5), sq_nonneg (y + 5)]
    have h2 : x ≤ 6 := by 
      nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 4), sq_nonneg (x + 4), sq_nonneg (y + 5)]
    have h3 : y ≤ 7 := by 
      nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 4), sq_nonneg (x + 4), sq_nonneg (y + 5)]
    have h4 : y ≥ -6 := by 
      nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 4), sq_nonneg (x + 4), sq_nonneg (y + 5)]
    interval_cases x <;> interval_cases y 
      <;> omega
  · -- Assume the set of solutions, prove the equation holds
    rintro (h | h | h | h | h | h)
    · -- (1, -5)
      rcases h with ⟨rfl, rfl⟩ 
      all_goals norm_num
    · -- (5, -5)
      rcases h with ⟨rfl, rfl⟩ 
      all_goals norm_num
    · -- (-4, 0)
      rcases h with ⟨rfl, rfl⟩ 
      all_goals norm_num
    · -- (5, 0)
      rcases h with ⟨rfl, rfl⟩ 
      all_goals norm_num
    · -- (-4, 4)
      rcases h with ⟨rfl, rfl⟩ 
      all_goals norm_num
    · -- (1, 4)
      rcases h with ⟨rfl, rfl⟩ 
      all_goals norm_num