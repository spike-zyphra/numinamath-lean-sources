import Mathlib

theorem algebra_12464 {x y : ℤ} (hx : x > 0) (hy : y > 0)
    (h1 : x * y + x + y = 71) (h2 : x ^ 2 * y + x * y ^ 2 = 880) :
    x ^ 2 + y ^ 2 = 146 := by 

  have eq3 : x ^ 2 * y + x * y ^ 2 = x * y * (x + y) := by 
    ring 
  rw [eq3] at h2
  
  have h3 : (x + 1) * (y + 1) = 72 := by 
    nlinarith

  have h5 : x + y = 16 := by 
    nlinarith [sq_nonneg (x * y - 16), sq_nonneg (x + y - 16), sq_nonneg (x * y - 55), sq_nonneg (x + y - 55),
      h1, h3]
  
  have h6 : x * y = 55 := by 
    nlinarith [h1, h5]

  nlinarith [h5, h6, sq_nonneg (x - 5), sq_nonneg (x - 11), sq_nonneg (y - 5), sq_nonneg (y - 11)]