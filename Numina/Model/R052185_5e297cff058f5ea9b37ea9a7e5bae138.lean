import Mathlib

theorem algebra_186661 (x y z w : ℝ)
    (h1 : 2*x+y+z+w=1)
    (h2 : x+3*y+z+w=2)
    (h3 : x+y+4*z+w=3)
    (h4 : x+y+z+5*w=25) :
    w=11/2 := by
  linarith