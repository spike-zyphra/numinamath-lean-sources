import Mathlib

theorem algebra_287160 {x y : ℝ} (hx : |x| + x + 5 * y = 2) (hy : |y| - y + x = 7) :
    x + y + 2009 = 2012 := by
  by_cases hx1 : x ≥ 0
  · -- If x ≥ 0, then |x| = x
    rw [abs_of_nonneg hx1] at hx
    by_cases hy1 : y ≥ 0
    · -- If y ≥ 0, then |y| = y
      rw [abs_of_nonneg hy1] at hy
      linarith
    · -- If y < 0, then |y| = -y
      rw [abs_of_neg (lt_of_not_ge hy1)] at hy
      linarith
  · -- If x < 0, then |x| = -x
    rw [abs_of_neg (lt_of_not_ge hx1)] at hx
    by_cases hy1 : y ≥ 0
    · -- If y ≥ 0, then |y| = y
      rw [abs_of_nonneg hy1] at hy
      linarith
    · -- If y < 0, then |y| = -y
      rw [abs_of_neg (lt_of_not_ge hy1)] at hy
      linarith