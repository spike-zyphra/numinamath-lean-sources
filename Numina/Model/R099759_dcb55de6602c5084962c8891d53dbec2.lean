import Mathlib

theorem algebra_261352 {a b c : ℤ} (ha : a + 5 = b) (hb : 5 + b = c) (hc : b + c = a) :
    b = -10 := by
  linarith