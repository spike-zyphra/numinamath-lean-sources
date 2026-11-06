import Mathlib

theorem algebra_146616 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x * 5 = y - 21) (h2 : (y - 21) * 9 / 10 = x * 5 / 10 + 9) :
    x = 8 ∧ y = 80 := by
  omega