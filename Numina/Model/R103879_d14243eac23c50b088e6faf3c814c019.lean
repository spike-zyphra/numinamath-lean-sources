import Mathlib

theorem algebra_2234 (a b c : ℝ) (ha : a ≠ 0) (h : ∃ x, x^2 + 3 * x + 5 = 0 ∧ a * x^2 + b * x + c = 0) :
    a + b + c ≥ 9 := by
  rcases h with ⟨x, hx1, hx2⟩
  have h1 : x^2 + 3 * x + 5 = 0 := by linarith
  have h2 : (x + 3 / 2) ^ 2 ≥ 0 := by
    apply sq_nonneg
  nlinarith