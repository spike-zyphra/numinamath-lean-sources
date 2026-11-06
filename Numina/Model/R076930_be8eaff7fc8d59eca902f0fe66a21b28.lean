import Mathlib

theorem algebra_188370 (x y z : ℝ) (h₀ : x + y + z = 3) (h₁ : x^2 + y^2 + z^2 = 3) :
    (x, y, z) = (1, 1, 1) := by 
  have h2 : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0 := by 
    nlinarith 
  have hx : (x - 1) ^ 2 = 0 := by 
    linarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have hy : (y - 1) ^ 2 = 0 := by 
    linarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have hz : (z - 1) ^ 2 = 0 := by 
    linarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have hx1 : x = 1 := by 
    nlinarith 
  have hy1 : y = 1 := by 
    nlinarith 
  have hz1 : z = 1 := by 
    nlinarith 
  exact Prod.ext hx1 (Prod.ext hy1 hz1)