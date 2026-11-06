import Mathlib

theorem algebra_93892 {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y)
(h1 : x + (2/3) * y = a) (h2 : x + (1/2) * y = b) :
x + y = 3 * a - 2 * b := by
  have eq1 : y = 6 * (a - b) := by 
    linarith
  have eq2 : x = 4 * b - 3 * a := by
    rw [eq1] at h2
    linarith
  linarith [eq1, eq2]