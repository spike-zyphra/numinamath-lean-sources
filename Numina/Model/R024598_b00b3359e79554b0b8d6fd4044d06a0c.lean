import Mathlib

theorem algebra_8243 {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : 1 = x) (h2 : x + y = y / x) (h3 : y / x = y) :
    x ^ 2012 + y ^ 2013 = 2 := by 
  have hx1 : x = 1 := by linarith
  rw [hx1] at h2
  field_simp at h2
  all_goals 
    linarith