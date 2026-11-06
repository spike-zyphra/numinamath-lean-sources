import Mathlib

theorem algebra_2273
    (x y z w : ℝ)
    (h1 : 1*x+4*y+2*z+w=27.6)
    (h2 : 2*x+6*y+2*z+2*w=32.2) :
    y+z=11.5 := by 
  have eq1 : w = 27.6 - x - 4 * y - 2 * z := by
    linarith
  rw [eq1] at h2
  ring_nf at h1 h2 ⊢
  linarith