import Mathlib

theorem algebra_168310 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) (x y z : ℝ) :
    a * x + b * y + c * z + b * x + c * y + a * z + c * x + a * y + b * z = x + y + z := by
  have h1 : a + b + c = 1 := h
  calc
    a * x + b * y + c * z + b * x + c * y + a * z + c * x + a * y + b * z
        = x * (a + b + c) + y * (a + b + c) + z * (a + b + c) := by ring
    _ = (x + y + z) * (a + b + c) := by ring
    _ = (x + y + z) * 1 := by rw [h1]
    _ = x + y + z := by ring