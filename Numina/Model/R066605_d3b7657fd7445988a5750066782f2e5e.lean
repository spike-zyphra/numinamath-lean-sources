import Mathlib

theorem algebra_1457 {a : ℤ} (ha : 0 < a) (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x + a * y = 5) (h2 : y - x = 1) :
    a = 1 ∨ a = 2 := by
  have eq1 : y = x + 1 := by
    linarith
  rw [eq1] at h1
  have h3 : a < 5 := by
    nlinarith [h1, hx, ha]
  have h4 : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
    omega
  rcases h4 with (rfl | rfl | rfl | rfl)
  · -- case a = 1
    left
    norm_num
  · -- case a = 2
    right
    norm_num
  · -- case a = 3
    exfalso
    omega
  · -- case a = 4
    exfalso
    omega