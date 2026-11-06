import Mathlib

theorem algebra_305061 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 60 = b * 55) (h2 : b = 2 * a) :
    a + b = 66 := by
  rw [show b = 2 * a by exact h2] at h1
  omega