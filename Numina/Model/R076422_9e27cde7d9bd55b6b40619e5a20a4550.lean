import Mathlib

theorem algebra_173234 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : (x * 1.4 + y * 1.2) = x + y + 1) (h2 : (x * 1.4 + y * 0.8) = x + y - 0.5)
    (h3 : (x * 1.4 + y * 1.6) = x + y + 4) :
    x + y = 15 := by
  ring_nf at h1 h2 h3
  linarith