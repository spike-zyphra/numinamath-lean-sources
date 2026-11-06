import Mathlib

theorem algebra_659
  {x y z : ℝ} (h1 : 2*x+4*y=116) (h2 : 3*x+8*y+z=441.2)
  (h3 : 2*x+6*y+z=116) : z=150 := by
  ring_nf at h1 h2 h3 ⊢
  linarith