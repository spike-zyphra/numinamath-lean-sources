import Mathlib

theorem algebra_288568 (a : ℝ) : (∃ x y, (x^2 + 4 * (y - a)^2 = 4 ∧ x^2 = 2 * y)) → (-1 ≤ a ∧ a ≤ 17 / 8) := by
  rintro ⟨x, y, h1, h2⟩
  have eq1 : 2 * y + 4 * (y - a) ^ 2 = 4 := by
    have h2_sub : x ^ 2 = 2 * y := h2
    rw [h2_sub] at h1
    nlinarith
  have eq2 : 4 * y ^ 2 + (2 - 8 * a) * y + (4 * a ^ 2 - 4) = 0 := by
    nlinarith [eq1]
  have h33 : (2 - 8 * a) ^ 2 - 4 * (4) * (4 * a ^ 2 - 4) ≥ 0 := by
    nlinarith [sq_nonneg (y + ( (2 - 8 * a) / 8 ) ) ]
  constructor
  · -- Show $-1 \leq a$
    nlinarith [sq_nonneg (x), sq_nonneg (y - 1), sq_nonneg (y - a), sq_nonneg (x - 0), sq_nonneg (a - 1), sq_nonneg (y - 17 / 8) ]
  · -- Show $a \leq 17 / 8$
    nlinarith