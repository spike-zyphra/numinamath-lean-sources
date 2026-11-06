import Mathlib

theorem algebra_3966 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : (1 - 1 / 5) * x = (1 - 1103 / y) * y)
    (h2 : (1 - 1 / 2) * (y - 1103) = (1 / 3) * y) :
    x + y = 6066.5 := by 
  field_simp [hy] at h1 h2
  ring_nf at h1 h2 ⊢
  nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy]