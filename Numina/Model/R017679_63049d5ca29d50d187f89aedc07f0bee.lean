import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11790 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = 1 ∧ t = x * y^2 * z^3} (1/432) := by
  constructor
  · -- Show 1/432 is in the set.
    use 1 / 6, 1 / 3, 1 / 2
    norm_num
  · -- Show that 1/432 is greatest
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, heq⟩
    have h2 : x * y^2 * z^3 ≤ 1 / 432 := by
      have h3 : x + y + z = 1 := h1
      have h5 : z = 1 - x - y := by 
        linarith
      rw [h5]
      nlinarith [sq_nonneg (x - 1 / 6), sq_nonneg (y - 1 / 3), sq_nonneg ((1 - x - y) - 1 / 2),
        mul_pos hx hy, mul_pos hy (show (1 - x - y : ℝ) > 0 by nlinarith), 
        mul_pos hx (show (1 - x - y : ℝ) > 0 by nlinarith),
        sq_nonneg (x * (y - 1 / 3)), sq_nonneg (y * (x - 1 / 6)), sq_nonneg ((1 - x - y) * (x - 1 / 6)), sq_nonneg ((1 - x - y) * (y - 1 / 3)), 
        mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < y by linarith),
        mul_pos (show (0 : ℝ) < y by linarith) (show (0 : ℝ) < 1 - x - y by nlinarith), 
        mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < 1 - x - y by nlinarith) 
      ]
    nlinarith [heq, h2]