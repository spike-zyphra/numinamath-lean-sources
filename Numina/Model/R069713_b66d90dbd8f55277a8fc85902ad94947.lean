import Mathlib

theorem algebra_224911 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 3) :
    a * b + b * c + 2 * c * a ≤ 9 / 2 := by
  have h1 : c = 3 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (b - 0), sq_nonneg ((3 - a - b) - 3 / 2), sq_nonneg (a - (3 - a - b)), sq_nonneg (b), sq_nonneg ((3 - a - b) - 3/2), sq_nonneg (a - 3/2), sq_nonneg (b - 0), sq_nonneg ((3 - a - b) - 3/2), sq_nonneg (a + (3 - a - b) - 3), sq_nonneg (b - 0), sq_nonneg (a + b - 3)]