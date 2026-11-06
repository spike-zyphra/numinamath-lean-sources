import Mathlib

theorem algebra_604432 (a : ℝ) (ha : a > 0) (h : a ^ 3 = 6 * (a + 1)) :
    ¬∃ x : ℝ, x ^ 2 + a * x + a ^ 2 - 6 = 0 := by
  intro h1
  rcases h1 with ⟨x, hx⟩
  have h3 : (x + a / 2) ^ 2 ≥ 0 := by apply sq_nonneg
  nlinarith [sq_nonneg (a ^ 2 - 8), sq_nonneg (a + 2), sq_nonneg (a - 4), sq_nonneg (x + 4), sq_nonneg (x + a / 2), sq_nonneg (x + a), sq_nonneg (x * a), sq_nonneg (a - 1), sq_nonneg (a * a - 8), mul_pos ha (show 0 < a by nlinarith), sq_nonneg (a * (a ^ 2 - 8)), sq_nonneg (a ^ 2 - 8), sq_nonneg (a ^ 2 - a), sq_nonneg (x * (x + a)), sq_nonneg (x + 2), sq_nonneg (x * a + 2), sq_nonneg (a ^ 2 - 4), sq_nonneg (a - 3)]