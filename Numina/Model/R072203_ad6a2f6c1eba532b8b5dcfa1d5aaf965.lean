import Mathlib

theorem algebra_21874 {b y : ℕ} (hb : b * 3 = y * 4) (hy : y ≠ 0)
    (h : (b + 5) * 3 = (y - 3) * 7) :
    b = 16 := by
  omega