import Mathlib

theorem algebra_8746 (x y : ℤ) : (x + y = x^2 - x * y + y^2) ↔
    (x = 0 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨ (x = 2 ∧ y = 2) := by
  constructor
  · -- Assume the equation $x + y = x^2 - x * y + y^2$, prove the possible integer pairs
    intro h_eq
    have h1 : x ≤ 4 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 2), sq_nonneg (y - 1)]
    have h2 : y ≤ 4 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 2)]
    have h3 : x ≥ -2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1)]
    have h4 : y ≥ -2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1)]
    interval_cases x <;> interval_cases y <;> 
      simp at h_eq ⊢ <;> tauto
  · -- Assume the possible integer pairs, prove the equation $x + y = x^2 - x * y + y^2$
    rintro (h | h | h | h | h | h)
    · -- (0, 0)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (0, 1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (1, 0)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (1, 2)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (2, 1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (2, 2)
      rcases h with ⟨rfl, rfl⟩
      norm_num