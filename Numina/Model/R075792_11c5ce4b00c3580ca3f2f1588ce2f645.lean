import Mathlib

theorem algebra_228349 (x y : ℝ) (h1 : 3*x+5*y=10.6) (h2 : 4*x+4*y=12) :
    x=2.2 := by
  have eq1 : x + y = 3 := by
    linarith [h2]
  have hy : y = 3 - x := by
    linarith [eq1]
  rw [hy] at h1
  have hx : x = 2.2 := by
    norm_num at h1 ⊢
    linarith
  exact hx