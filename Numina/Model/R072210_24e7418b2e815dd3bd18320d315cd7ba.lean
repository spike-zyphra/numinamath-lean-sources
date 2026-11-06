import Mathlib

theorem algebra_252509 (a : ℝ) (ha : 0 < a) (h : ∃ r, a * r = a + 1 ∧ a * r^2 = a + 2 ∧ a * r^3 = a + 3) :
    a = 5 := by
  rcases h with ⟨r, h1, h2, h3⟩
  nlinarith [sq_nonneg (a - 5), sq_nonneg (r - 2)]