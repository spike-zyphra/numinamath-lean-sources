import Mathlib

theorem algebra_105394 (x : ℝ) (hx : x^2 + 2 * x + 2 ≠ 0) :
    (2 * x + 2) / (x^2 + 2 * x + 2) + x^4 - 8 * x^2 + 17 = 0 ↔ x = -2 := by
  constructor
  · -- Forward direction: if equation equals 0, then x = -2
    intro h
    have heq : (2 * x + 2) / (x^2 + 2 * x + 2) = -x^4 + 8 * x^2 - 17 := by linarith
    have heq2 : 2 * x + 2 = (-x^4 + 8 * x^2 - 17) * (x^2 + 2 * x + 2) := by
      have h1 : x^2 + 2 * x + 2 ≠ 0 := hx
      field_simp [h1] at heq ⊢
      linarith
    have h1 : x = -2 := by
      nlinarith [sq_nonneg (x^2 - 4), sq_nonneg ((x + 2)^2), sq_nonneg (x^2 + 2 * x + 2), sq_pos_of_ne_zero (show (x^2 + 2 * x + 2 : ℝ) ≠ 0 by assumption), sq_nonneg (x + 2), sq_nonneg (x^2 - 1)]
    linarith
  · -- Reverse direction: if x = -2, then equation equals 0
    intro h
    rw [h]
    norm_num