import Mathlib

theorem algebra_171942 {x y o : ℝ} (hx : x = 150000) (hy : y = 290000)
    (h : x * 0.80 + y * 0.862 + o = 1350000 * 1.001) :
    x + y + o = 1421370 ∧ 
    (x + y + o) / 1350000 = 1421370 / 1350000 := by
  have : x + y + o = 1421370 := by linarith
  rw [this]
  norm_num