import Mathlib

theorem algebra_198006 {x : ℕ} (hx : x > 0) (h : 12 * x = (x + 12) * (x + 1)) :
    x = 49 := by
  nlinarith [h, sq_nonneg (x - 49), sq_nonneg (x + 48)]