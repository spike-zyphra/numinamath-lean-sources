import Mathlib

theorem algebra_164317 {a b : ℕ} (ha : b = 4 * a) (hb : a + 60 = b - 60) :
    a = 40 := by
  rw [show b = 4 * a by exact ha] at hb
  omega