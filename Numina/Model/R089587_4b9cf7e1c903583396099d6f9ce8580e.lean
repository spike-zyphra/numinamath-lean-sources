import Mathlib

theorem algebra_269390 (x y : ℤ) (hx : x = 314) (hy : y = 565) :
    187 * x - 104 * y ≠ 41 := by
  rw [hx, hy]
  -- Now we need to show that 187 * 314 - 104 * 565 ≠ 41
  norm_num