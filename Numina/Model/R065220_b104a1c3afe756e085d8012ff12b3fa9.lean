import Mathlib

theorem inequalities_294083 (x : ℝ) (hx : x ≥ 0) :
    1 + x^2 + x^6 + x^8 ≥ 4 * x^4 ∧
    (1 + x^2 + x^6 + x^8 = 4 * x^4 ↔ x = 1) := by
  constructor
  · -- First part: proving the inequality 1 + x^2 + x^6 + x^8 ≥ 4 * x^4
    nlinarith [sq_nonneg (x^4 - x^2), sq_nonneg (x^2 - 1), sq_nonneg (x^2 - x), sq_nonneg (x - 1), sq_nonneg (x^2 - x^4), sq_nonneg (x^4 - x^2), sq_nonneg (x^4 - 1), sq_nonneg (x^2 + 1), sq_nonneg (x^2 + x +1), sq_nonneg (x^2 - x +1)]
  · -- Second part: proving the equality condition 1 + x^2 + x^6 + x^8 = 4 * x^4 ↔ x = 1
    constructor
    · -- Forward direction: assuming 1 + x^2 + x^6 + x^8 = 4 * x^4, proving x = 1
      intro h
      have h1 : 1 + x^2 + x^6 + x^8 = 4 * x^4 := h
      nlinarith [sq_nonneg (x^4 - x^2), sq_nonneg (x^2 - 1), sq_nonneg (x^2 - x), sq_nonneg (x - 1), sq_nonneg (x^2 - x^4), sq_nonneg (x^4 - x^2), sq_nonneg (x^4 - 1), sq_nonneg (x^2 + 1), sq_nonneg (x^2 + x +1), sq_nonneg (x^2 - x +1)]
    · -- Backward direction: assuming x = 1, proving 1 + x^2 + x^6 + x^8 = 4 * x^4
      intro h
      rw [h]
      norm_num