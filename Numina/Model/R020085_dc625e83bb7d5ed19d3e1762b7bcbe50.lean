import Mathlib

open Finset Real

theorem algebra_208582 {x : ℕ → ℚ} (hx : ∀ n, x (n + 1) = x n ^ 2 - x n + 1)
    (hx1 : x 1 = 1 / 2) :
    ∑' i, 1 / x i = 1 := by 
  have h1 := hx 0
  rw [show x 1 = 1 / 2 by linarith [hx1]] at h1
  have h2 : x 0 ^ 2 - x 0 + 1 / 2 = 0 := by
    nlinarith [h1]
  have h3 : x 0 ^ 2 - x 0 + 1 / 2 > 0 := by
    nlinarith [sq_nonneg (x 0 - 1 / 2)]
  nlinarith [h2, h3]