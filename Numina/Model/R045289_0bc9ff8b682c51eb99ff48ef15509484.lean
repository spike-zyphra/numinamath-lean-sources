import Mathlib

theorem algebra_20572 {x y : ℝ} (h1 : 2*x-3*y=-3.2-0.2*x+0.1*y) (h2 : x=0.6*x-y+8.8) :
    (x,y)=(7,6) := by
  have eq1 : 22 * x - 31 * y = -32 := by
    ring_nf at h1 ⊢
    linarith
  have eq2 : 4 * x + 10 * y = 88 := by
    ring_nf at h2 ⊢
    linarith
  have hx : x = 7 := by
    linarith [eq1, eq2]
  have hy : y = 6 := by
    linarith [eq2, hx]
  simp [Prod.ext_iff, hx, hy]