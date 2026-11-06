import Mathlib

theorem algebra_170194 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : 3 * x ^ 2 + 7 * x * y - 2 * x - 5 * y - 35 = 0) :
    x = 1 ∧ y = 17 ∨ x = 2 ∧ y = 3 := by
  have h1 : 3 * x ^ 2 + 7 * x * y - 2 * x - 5 * y - 35 = 0 := h
  have h4 : x < 4 := by
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y), sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (x - 1), sq_nonneg (y - 17)]
  have h5 : x = 1 ∨ x = 2 ∨ x = 3 := by
    omega
  rcases h5 with (rfl | rfl | rfl)
  · -- Case x = 1, solve for y
    have h6 : y = 17 := by
      nlinarith
    left
    exact ⟨by trivial, h6⟩
  · -- Case x = 2, solve for y
    have h7 : y = 3 := by
      nlinarith
    right
    exact ⟨by trivial, h7⟩
  · -- Case x = 3, show contradiction
    omega