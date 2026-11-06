import Mathlib

theorem algebra_286609 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : (x + y) ^ 2 = 2500 ∧ x * y = 500) :
    x ^ 3 + y ^ 3 = 50000 := by 
  rcases h with ⟨h1, h2⟩
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy]