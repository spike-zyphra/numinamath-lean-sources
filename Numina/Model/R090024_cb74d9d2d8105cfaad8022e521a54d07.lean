import Mathlib

theorem algebra_38934 {b t : ℕ} (hb : b = t + 15) (ht : 3 * t = 2 * b + 15) :
    b + t = 105 := by
  rw [hb] at ht
  omega