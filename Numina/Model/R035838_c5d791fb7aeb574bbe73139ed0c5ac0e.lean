import Mathlib

theorem algebra_221526 (a : ℝ) (h : a^5 - a^3 + a = 2) :
    3 < a^6 ∧ a^6 < 4 := by
  have h1 : a > 1 := by
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (a^2 - a), sq_nonneg (a^2 + 1), sq_nonneg (a^3 - a^2), sq_nonneg (a^2 - a), sq_nonneg (a - 1), sq_nonneg (a^2 - 1), h]
  have h2 : a < 2 := by
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (a^2 - a), sq_nonneg (a^2 + 1), sq_nonneg (a^3 - a^2), sq_nonneg (a^2 - a), sq_nonneg (a - 1), sq_nonneg (a^2 - 1), h, sq_nonneg (a - 2)]
  have h3 : 3 < a^6 := by
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a^3 - 1), sq_nonneg (a - 1), sq_nonneg (a^2 - a), sq_nonneg (a + 1), sq_nonneg (a^3 - a^2), h1, h, mul_pos (sub_pos.mpr h1) (sub_pos.mpr h1), sq_nonneg (a^4 - a^2), sq_nonneg (a^4 - 1)]
  have h4 : a^6 < 4 := by
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a^3 - 1), sq_nonneg (a - 1), sq_nonneg (a^2 - a), sq_nonneg (a + 1), sq_nonneg (a^3 - a^2), h2, h, mul_pos (sub_pos.mpr h1) (sub_pos.mpr h1), sq_nonneg (a^4 - a^2), sq_nonneg (a^4 - 1)]
  constructor <;> try linarith
  <;> try linarith