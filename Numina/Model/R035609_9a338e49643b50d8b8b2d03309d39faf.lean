import Mathlib

theorem algebra_172407 (x y : ℝ) :
    x^3 + y^2 ≠ 2 ∨ x^2 + x * y + y^2 - y ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨h1, h2⟩
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 1), sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg (x - y), sq_nonneg (x + 1/2), sq_nonneg (y + 1/2), sq_nonneg (x * y), sq_nonneg ((x - 1) * y), sq_nonneg ((x - 1) * (x + 1)), sq_nonneg ((y - 1) * (y + 1)), sq_nonneg ((x * (x - 1))), sq_nonneg ((y * (y - 1)))]