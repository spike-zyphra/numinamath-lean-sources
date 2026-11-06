import Mathlib

theorem algebra_301346 {x y : ℝ}
    (hx : (x - 11)^5 + 15 * (x - 11) = 5) (hy : (y - 4)^5 + 15 * (y - 4) = -5) :
    x + y = 15 := by
  have h1 : (x - 11) ^ 5 + 15 * (x - 11) + ((y - 4) ^ 5 + 15 * (y - 4)) = 0 := by
    linarith [hx, hy]
  have h2 : (x - 11) ^ 5 + (y - 4) ^ 5 + 15 * (x + y - 15) = 0 := by
    nlinarith
  have h3 : (x + y - 15) = 0 := by
    nlinarith [sq_nonneg ((x - 11) - (y - 4)), sq_nonneg ((x - 11) + (y - 4)), 
      sq_nonneg ((x - 11) ^ 2 - (y - 4) ^ 2), sq_nonneg ((x - 11) ^ 2 + (y - 4) ^ 2), 
      sq_nonneg ((x - 11) * (y - 4)), 
      sq_nonneg ((x - 11) ^ 4 - (x - 11) ^ 2 * (y - 4) ^ 2 + (y - 4) ^ 4)]
  linarith