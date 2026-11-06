import Mathlib

theorem algebra_67365 {x y : ℝ} (hxy : x = y * (3 - y)^2 ∧ y = x * (3 - x)^2) :
    x + y = 0 ∨ x + y = 3 ∨ x + y = 4 ∨ x + y = 5 ∨ x + y = 8 := by
  rcases hxy with ⟨hx, hy⟩
  have h1 : (x + y - 0) * (x + y - 3) * (x + y - 4) * (x + y - 5) * (x + y - 8) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x * y), sq_nonneg ((x + y) - 4), sq_nonneg ((x - 3) + (y - 3)), sq_nonneg ((x - 3) - (y - 3))]
  cases' (mul_eq_zero.mp h1) with h2 h1
  cases' (mul_eq_zero.mp h2) with h2 h1
  cases' (mul_eq_zero.mp h2) with h2 h1
  cases' (mul_eq_zero.mp h2) with h2 h1
  · -- Case $x + y - 0 = 0$.
    left
    linarith
  · -- Case $x + y - 3 = 0$.
    right
    left
    linarith
  · -- Case $x + y - 4 = 0$.
    right
    right
    left
    linarith
  · -- Case $x + y - 5 = 0$.
    right
    right
    right
    left
    linarith
  · -- Case $x + y - 8 = 0$.
    right
    right
    right
    right
    linarith