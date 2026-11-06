import Mathlib

theorem algebra_294632 {x : ℝ} (hx : 0 < x) (C S : ℝ)
    (hC : C = 2 * 73) (hS : S = 100 * (1 - x / 100)) (hS' : S * (1 + x / 100) = C + 1 + 1 / 9) :
    x = 10 := by
  rw [hC] at hS'
  rw [hS] at hS'
  nlinarith [sq_nonneg (x - 10), sq_nonneg (x + 10)]