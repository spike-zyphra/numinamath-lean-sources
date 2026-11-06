import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_4919 :
  IsLeast {s : ℝ | ∃ x y : ℝ, s = 1998 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2} 1997 := by 
  constructor
  · -- Show that 1997 is achievable by finding x, y such that 1997 = 1998 + x^4*y^2 + x^2*y^4 - 3*x^2*y^2 
    use 1, 1
    norm_num
  · -- Show that 1997 is indeed the least
    intro s hs
    rcases hs with ⟨x, y, h_eq⟩
    nlinarith [sq_nonneg (x^2 * y - x * y^2), sq_nonneg (x^2 - y^2), sq_nonneg (x * y), sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (x * y - 1), sq_nonneg (x * y + 1), mul_nonneg (sq_nonneg (x)) (sq_nonneg (y)), sq_nonneg (x^2 * y - x * y^2), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 1), sq_nonneg (x * y + 1)]