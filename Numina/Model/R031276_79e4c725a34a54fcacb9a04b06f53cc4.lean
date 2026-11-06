import Mathlib

theorem algebra_5021 {k : ℝ} (h : ∃ x y, y = x^2 + (k + 1)*x + (3*k + 5) ∧
y = x^2 + (2*k + 3)*x + (2*k + 7) ∧ y = x^2 + (3*k - 1)*x + (k + 6)) :
k = 2 / 3 := by

  rcases h with ⟨x, y, h1, h2, h3⟩
  have eq1 : (-k - 2) * x + (k - 2) = 0 := by
    nlinarith
  have eq2 : (-2*k + 2) * x + (2*k - 1) = 0 := by
    nlinarith

  nlinarith [sq_nonneg (x + 1), sq_nonneg (k - 2 / 3), sq_nonneg (x * (k + 2)), sq_nonneg ((k - 2 / 3) * (x)), sq_nonneg ((k - 2 / 3) * (x + 1))]