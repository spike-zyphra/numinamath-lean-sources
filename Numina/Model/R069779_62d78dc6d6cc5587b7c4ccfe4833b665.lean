import Mathlib

theorem algebra_199974 (x y : ℤ) :
    x^2 - 12 * x + y^2 + 2 = 0 ↔
    (x = 11 ∧ y = 3) ∨ (x = 1 ∧ y = 3) ∨ (x = 11 ∧ y = -3) ∨ (x = 1 ∧ y = -3) ∨
    (x = 9 ∧ y = 5) ∨ (x = 3 ∧ y = 5) ∨ (x = 9 ∧ y = -5) ∨ (x = 3 ∧ y = -5) := by
  constructor
  · -- Assume x^2 - 12x + y^2 + 2 = 0, prove the 8 solutions
    intro h
    have h₁ : x^2 - 12 * x + y^2 + 2 = 0 := h
    have h4 : (x - 6) ^ 2 + y ^ 2 = 34 := by
      nlinarith
    have hy1 : y ≤ 5 := by
      nlinarith [sq_nonneg (x - 6), sq_nonneg y]
    have hy2 : y ≥ -6 := by
      nlinarith [sq_nonneg (x - 6), sq_nonneg y]
    have hx1 : x ≤ 11 := by
      nlinarith [sq_nonneg (y), sq_nonneg (x - 6)]
    have hx2 : x ≥ 0 := by
      nlinarith [sq_nonneg (y), sq_nonneg (x - 6)]
    interval_cases y <;> interval_cases x <;> omega
  · -- Assume one of the 8 solutions, prove x^2 - 12x + y^2 + 2 = 0
    rintro (h | h | h | h | h | h | h | h)
    · -- Case (11, 3)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (1, 3)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (11, -3)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (1, -3)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (9, 5)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (3, 5)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (9, -5)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (3, -5)
      rcases h with ⟨rfl, rfl⟩
      norm_num