import Mathlib

theorem algebra_122853 (a b : ℝ) (h : ∃ x ∈ Set.Icc 1 2, x^2 + a * x + b - 3 = 0) :
    a^2 + (b - 4)^2 ≥ 2 := by

  rcases h with ⟨x, ⟨hx1, hx2⟩, h_eq⟩
  have h1 : 1 ≤ x := by
    linarith [hx1]
  have h2 : x ≤ 2 := by
    linarith [hx2]

  have h_eq2 : b = 3 - x^2 - a * x := by
    linarith
  rw [h_eq2]
  nlinarith [sq_nonneg (a + (x^3 + x) / (1 + x^2)), sq_nonneg ((-x^2 - a * x - 1) + 1),
          sq_nonneg (x - 1), sq_nonneg (x - 2),
          sq_nonneg (a + 1), sq_nonneg ((x - 1) * (x + 1)), sq_nonneg (x^2 - 1),
          mul_nonneg (show (0 : ℝ) ≤ x - 1 by nlinarith) (show (0 : ℝ) ≤ 2 - x by nlinarith)]