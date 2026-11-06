import Mathlib

/- What is the least possible value of (xy−1)^2+(x+y)^2 for real numbers x and y?
(A) 0
(B) 14
(C) 12
(D) 1
-/


theorem algebra_94241 :
IsLeast {t : ℝ | ∃ x y, t = (x * y - 1)^2 + (x + y)^2} 1 := by
  -- split to two goals, 1 belongs to set and 1 is a lower bound
  constructor
  -- first case, we need x, y so that (x*y-1)^2 + (x+y)^2 = 1, use 0 for both and calculate to show true
  . simp
    use 0
    use 0
    norm_num
  -- next we need to prove for all t = (x * y - 1)^2 + (x+y)^2 >= 1, introduce variables to get 1 ≤ (x * y - 1)^2 + (x + y)^2. rhs is expanded to get 1 + x^2 + y^2 + (xy)^2. since squares are nonnegative, inequality follows using that
  . unfold lowerBounds
    simp
    intro t x y h
    rw [h]
    calc
    1 ≤ 1 + x^2 := by
      apply (le_add_iff_nonneg_right 1).mpr
      exact sq_nonneg x
    _ ≤ 1 + x^2 + y^2 := by
      apply (le_add_iff_nonneg_right (1 + x^2)).mpr
      exact sq_nonneg y
    _ ≤ 1 + x^2 + y^2 + (x * y)^2 := by
      apply (le_add_iff_nonneg_right (1 + x^2 + y^2)).mpr
      exact sq_nonneg (x*y)
    _ = (x * y - 1)^2 + (x + y)^2 := by ring