import Mathlib

theorem algebra_835 {n m : ℕ} (h1 : n = m) (h2 : 240 * n = 240 * m + 240 * 9) :
    240 * n - 240 * m = 960 := by
  omega