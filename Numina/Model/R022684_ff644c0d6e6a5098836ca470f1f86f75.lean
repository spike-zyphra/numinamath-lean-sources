import Mathlib

theorem algebra_199681 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x = y - 8) (h2 : 1 / y = 2 / x + 1.5 / (x + y)) :
    x = 4 ∧ y = 6 := by
  have hx1 : x ≠ 0 := by linarith
  have hy1 : y ≠ 0 := by linarith
  have hxy1 : x + y > 0 := by
    nlinarith
  have eq2 : x * (x + y) = 2 * y * (x + y) + 1.5 * (x * y) := by
    have eq3 : x ≠ 0 := hx1
    have eq4 : y ≠ 0 := hy1
    have eq5 : x + y ≠ 0 := by
      nlinarith
    field_simp [hx1, hy1, eq5] at h2 ⊢
    nlinarith [h2, mul_pos hx hy, mul_pos hx (show 0 < x + y by linarith), mul_pos hy (show 0 < x + y by linarith)]
  rw [show x = y - 8 by linarith [h1]] at eq2
  ring_nf at eq2
  nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_nonneg (y - 6), sq_nonneg (y + (16 / 7)), sq_nonneg (y * (y - 6)), sq_nonneg ((y - 8 / 7) * 7)]