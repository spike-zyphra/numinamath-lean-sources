import Mathlib

theorem algebra_228415 {x y z : ℝ} (h1 : x > 0) (h2 : y > 0) (h3 : z > 0)
    (h4 : (x / 5) + (y / 2.5) + (z / 2) = 160) (h5 : (x / 2) + (y / 3) + (z / 4) = 240) :
    x + y + z = 560 := by 
  ring_nf at h4 h5 ⊢
  linarith