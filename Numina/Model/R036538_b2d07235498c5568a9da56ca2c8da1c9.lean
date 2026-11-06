import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_320772 (x y : ℝ) (h : 17*(x^2+y^2)-30*x*y-16=0) :
    sqrt (16*x^2+4*y^2-16*x*y-12*x+6*y+9) ≤ 7 := by 

  have h1 : (16 * x ^ 2 + 4 * y ^ 2 - 16 * x * y - 12 * x + 6 * y + 9 ) ≤ 49 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (4 * x - 2 * y - 5), sq_nonneg (4 * x - 2 * y + 5), 
      sq_nonneg (x - (4 * x - 2 * y)/4), sq_nonneg (y - (4 * x - 2 * y)/4 * (1/2)), 
      sq_nonneg (x + 19 / 10), sq_nonneg (y + 13 / 10),
      sq_nonneg ((x - y) - (1/1)), sq_nonneg ((4 * x - 2 * y) - (5)), sq_nonneg ((4 * x - 2 * y) + (5)), 
      h]

  have h2 : Real.sqrt (16 * x ^ 2 + 4 * y ^ 2 - 16 * x * y - 12 * x + 6 * y + 9) ≤ Real.sqrt (49 : ℝ) := by 
    apply Real.sqrt_le_sqrt 
    nlinarith 
  have h3 : Real.sqrt (49 : ℝ) = 7 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
  rw [h3] at h2 
  exact h2